import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25856 raw25856Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw25856 raw25856Labels = mixedMoment B raw25856step0 raw25856step0Labels := by
      have hz : ∀ j, raw25856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25856step0 = (fun i j => raw25856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25856step0 raw25856; decide +kernel
      have hl : raw25856step0Labels = raw25856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25856 raw25856Labels permutation265 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw25857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25857 raw25857Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25857 raw25857Labels = mixedMoment B raw25857step0 raw25857step0Labels := by
      have hz : ∀ j, raw25857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25857step0 = (fun i j => raw25857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25857step0 raw25857; decide +kernel
      have hl : raw25857step0Labels = raw25857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25857 raw25857Labels permutation346 hz
    mixedMoment B raw25857step0 raw25857step0Labels = mixedMoment B raw25857step1 raw25857step1Labels := by
      have hz : ∀ j, raw25857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25857step1 = (fun i j => raw25857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25857step1 raw25857step0; decide +kernel
      have hl : raw25857step1Labels = raw25857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25857step0 raw25857step0Labels permutation56 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25858 raw25858Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25858 raw25858Labels = mixedMoment B raw25858step0 raw25858step0Labels := by
      have hz : ∀ j, raw25858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25858step0 = (fun i j => raw25858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25858step0 raw25858; decide +kernel
      have hl : raw25858step0Labels = raw25858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25858 raw25858Labels permutation346 hz
    mixedMoment B raw25858step0 raw25858step0Labels = mixedMoment B raw25858step1 raw25858step1Labels := by
      have hz : ∀ j, raw25858step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25858step1 = (fun i j => raw25858step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25858step1 raw25858step0; decide +kernel
      have hl : raw25858step1Labels = raw25858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25858step0 raw25858step0Labels permutation56 hz
    mixedMoment B raw25858step1 raw25858step1Labels = mixedMoment B raw25858step2 raw25858step2Labels := by
      have ha : raw25858step2 = (fun i j => raw25858step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25858step2 raw25858step1; decide +kernel
      have hl : raw25858step2Labels = raw25858step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25858step1 raw25858step1Labels permutation10 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25859step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25859step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25859step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25859 raw25859Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25859 raw25859Labels = mixedMoment B raw25859step0 raw25859step0Labels := by
      have hz : ∀ j, raw25859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25859step0 = (fun i j => raw25859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25859step0 raw25859; decide +kernel
      have hl : raw25859step0Labels = raw25859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25859 raw25859Labels permutation346 hz
    mixedMoment B raw25859step0 raw25859step0Labels = mixedMoment B raw25859step1 raw25859step1Labels := by
      have hz : ∀ j, raw25859step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25859step1 = (fun i j => raw25859step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25859step1 raw25859step0; decide +kernel
      have hl : raw25859step1Labels = raw25859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25859step0 raw25859step0Labels permutation56 hz
    mixedMoment B raw25859step1 raw25859step1Labels = mixedMoment B raw25859step2 raw25859step2Labels := by
      have hz : ∀ i, raw25859step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw25859step2 = (fun i j => raw25859step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw25859step2 raw25859step1; decide +kernel
      have hl : raw25859step2Labels = (fun j => raw25859step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw25859step1 raw25859step1Labels permutation4 hz
    mixedMoment B raw25859step2 raw25859step2Labels = mixedMoment B raw25859step3 raw25859step3Labels := by
      have ha : raw25859step3 = raw25859step2 := by apply Matrix.ext; unfold raw25859step3 raw25859step2; decide +kernel
      have hl : raw25859step2Labels = labelEmbedding2 ∘ raw25859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25859step2 raw25859step2Labels raw25859step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw25860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25860 raw25860Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25860 raw25860Labels = mixedMoment B raw25860step0 raw25860step0Labels := by
      have hz : ∀ j, raw25860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25860step0 = (fun i j => raw25860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25860step0 raw25860; decide +kernel
      have hl : raw25860step0Labels = raw25860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25860 raw25860Labels permutation346 hz
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw25861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25861 raw25861Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25861 raw25861Labels = mixedMoment B raw25861step0 raw25861step0Labels := by
      have ha : raw25861step0 = (fun i j => raw25861 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25861step0 raw25861; decide +kernel
      have hl : raw25861step0Labels = raw25861Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25861 raw25861Labels permutation176 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw25862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25862 raw25862Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25862 raw25862Labels = mixedMoment B raw25862step0 raw25862step0Labels := by
      have hz : ∀ j, raw25862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25862step0 = (fun i j => raw25862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25862step0 raw25862; decide +kernel
      have hl : raw25862step0Labels = raw25862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25862 raw25862Labels permutation346 hz
    mixedMoment B raw25862step0 raw25862step0Labels = mixedMoment B raw25862step1 raw25862step1Labels := by
      have ha : raw25862step1 = (fun i j => raw25862step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25862step1 raw25862step0; decide +kernel
      have hl : raw25862step1Labels = raw25862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25862step0 raw25862step0Labels permutation38 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25863 raw25863Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25863 raw25863Labels = mixedMoment B raw25863step0 raw25863step0Labels := by
      have hz : ∀ j, raw25863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25863step0 = (fun i j => raw25863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25863step0 raw25863; decide +kernel
      have hl : raw25863step0Labels = raw25863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25863 raw25863Labels permutation346 hz
    mixedMoment B raw25863step0 raw25863step0Labels = mixedMoment B raw25863step1 raw25863step1Labels := by
      have ha : raw25863step1 = (fun i j => raw25863step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25863step1 raw25863step0; decide +kernel
      have hl : raw25863step1Labels = raw25863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25863step0 raw25863step0Labels permutation44 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25864 raw25864Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25864 raw25864Labels = mixedMoment B raw25864step0 raw25864step0Labels := by
      have hz : ∀ j, raw25864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25864step0 = (fun i j => raw25864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25864step0 raw25864; decide +kernel
      have hl : raw25864step0Labels = raw25864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25864 raw25864Labels permutation346 hz
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw25865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25865 raw25865Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25865 raw25865Labels = mixedMoment B raw25865step0 raw25865step0Labels := by
      have hz : ∀ j, raw25865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25865step0 = (fun i j => raw25865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25865step0 raw25865; decide +kernel
      have hl : raw25865step0Labels = raw25865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25865 raw25865Labels permutation265 hz
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw25866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25866 raw25866Labels = mixedMoment B node4344 node4344Labels := by
  calc
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw25867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25867 raw25867Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25867 raw25867Labels = mixedMoment B raw25867step0 raw25867step0Labels := by
      have hz : ∀ j, raw25867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25867step0 = (fun i j => raw25867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25867step0 raw25867; decide +kernel
      have hl : raw25867step0Labels = raw25867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25867 raw25867Labels permutation265 hz
    mixedMoment B raw25867step0 raw25867step0Labels = mixedMoment B raw25867step1 raw25867step1Labels := by
      have ha : raw25867step1 = (fun i j => raw25867step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25867step1 raw25867step0; decide +kernel
      have hl : raw25867step1Labels = raw25867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25867step0 raw25867step0Labels permutation38 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25868 raw25868Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25868 raw25868Labels = mixedMoment B raw25868step0 raw25868step0Labels := by
      have hz : ∀ j, raw25868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25868step0 = (fun i j => raw25868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25868step0 raw25868; decide +kernel
      have hl : raw25868step0Labels = raw25868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25868 raw25868Labels permutation265 hz
    mixedMoment B raw25868step0 raw25868step0Labels = mixedMoment B raw25868step1 raw25868step1Labels := by
      have ha : raw25868step1 = (fun i j => raw25868step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25868step1 raw25868step0; decide +kernel
      have hl : raw25868step1Labels = raw25868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25868step0 raw25868step0Labels permutation44 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25869 raw25869Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25869 raw25869Labels = mixedMoment B raw25869step0 raw25869step0Labels := by
      have hz : ∀ j, raw25869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25869step0 = (fun i j => raw25869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25869step0 raw25869; decide +kernel
      have hl : raw25869step0Labels = raw25869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25869 raw25869Labels permutation265 hz
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw25870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25870 raw25870Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw25870 raw25870Labels = mixedMoment B raw25870step0 raw25870step0Labels := by
      have hz : ∀ j, raw25870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25870step0 = (fun i j => raw25870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25870step0 raw25870; decide +kernel
      have hl : raw25870step0Labels = raw25870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25870 raw25870Labels permutation346 hz
    mixedMoment B raw25870step0 raw25870step0Labels = mixedMoment B raw25870step1 raw25870step1Labels := by
      have hz : ∀ j, raw25870step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25870step1 = (fun i j => raw25870step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25870step1 raw25870step0; decide +kernel
      have hl : raw25870step1Labels = raw25870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25870step0 raw25870step0Labels permutation56 hz
    mixedMoment B raw25870step1 raw25870step1Labels = mixedMoment B raw25870step2 raw25870step2Labels := by
      have ha : raw25870step2 = (fun i j => raw25870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25870step2 raw25870step1; decide +kernel
      have hl : raw25870step2Labels = raw25870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25870step1 raw25870step1Labels permutation10 permutation2
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw25871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25871 raw25871Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25871 raw25871Labels = mixedMoment B raw25871step0 raw25871step0Labels := by
      have hz : ∀ j, raw25871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25871step0 = (fun i j => raw25871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25871step0 raw25871; decide +kernel
      have hl : raw25871step0Labels = raw25871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25871 raw25871Labels permutation346 hz
    mixedMoment B raw25871step0 raw25871step0Labels = mixedMoment B raw25871step1 raw25871step1Labels := by
      have ha : raw25871step1 = (fun i j => raw25871step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25871step1 raw25871step0; decide +kernel
      have hl : raw25871step1Labels = raw25871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25871step0 raw25871step0Labels permutation34 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw25872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25872 raw25872Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25872 raw25872Labels = mixedMoment B raw25872step0 raw25872step0Labels := by
      have hz : ∀ j, raw25872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25872step0 = (fun i j => raw25872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25872step0 raw25872; decide +kernel
      have hl : raw25872step0Labels = raw25872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25872 raw25872Labels permutation265 hz
    mixedMoment B raw25872step0 raw25872step0Labels = mixedMoment B raw25872step1 raw25872step1Labels := by
      have ha : raw25872step1 = (fun i j => raw25872step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25872step1 raw25872step0; decide +kernel
      have hl : raw25872step1Labels = raw25872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25872step0 raw25872step0Labels permutation34 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw25873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw25873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25873 raw25873Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25873 raw25873Labels = mixedMoment B raw25873step0 raw25873step0Labels := by
      have hz : ∀ j, raw25873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25873step0 = (fun i j => raw25873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25873step0 raw25873; decide +kernel
      have hl : raw25873step0Labels = raw25873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25873 raw25873Labels permutation346 hz
    mixedMoment B raw25873step0 raw25873step0Labels = mixedMoment B raw25873step1 raw25873step1Labels := by
      have hz : ∀ j, raw25873step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25873step1 = (fun i j => raw25873step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25873step1 raw25873step0; decide +kernel
      have hl : raw25873step1Labels = raw25873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25873step0 raw25873step0Labels permutation56 hz
    mixedMoment B raw25873step1 raw25873step1Labels = mixedMoment B raw25873step2 raw25873step2Labels := by
      have ha : raw25873step2 = (fun i j => raw25873step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25873step2 raw25873step1; decide +kernel
      have hl : raw25873step2Labels = raw25873step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25873step1 raw25873step1Labels permutation10 permutation2
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw25874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25874 raw25874Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25874 raw25874Labels = mixedMoment B raw25874step0 raw25874step0Labels := by
      have hz : ∀ j, raw25874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25874step0 = (fun i j => raw25874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25874step0 raw25874; decide +kernel
      have hl : raw25874step0Labels = raw25874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25874 raw25874Labels permutation346 hz
    mixedMoment B raw25874step0 raw25874step0Labels = mixedMoment B raw25874step1 raw25874step1Labels := by
      have hz : ∀ j, raw25874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25874step1 = (fun i j => raw25874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25874step1 raw25874step0; decide +kernel
      have hl : raw25874step1Labels = raw25874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25874step0 raw25874step0Labels permutation56 hz
    mixedMoment B raw25874step1 raw25874step1Labels = mixedMoment B raw25874step2 raw25874step2Labels := by
      have ha : raw25874step2 = (fun i j => raw25874step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25874step2 raw25874step1; decide +kernel
      have hl : raw25874step2Labels = raw25874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25874step1 raw25874step1Labels permutation11 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw25875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25875 raw25875Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw25875 raw25875Labels = mixedMoment B raw25875step0 raw25875step0Labels := by
      have hz : ∀ j, raw25875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25875step0 = (fun i j => raw25875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25875step0 raw25875; decide +kernel
      have hl : raw25875step0Labels = raw25875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25875 raw25875Labels permutation346 hz
    mixedMoment B raw25875step0 raw25875step0Labels = mixedMoment B raw25875step1 raw25875step1Labels := by
      have hz : ∀ j, raw25875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25875step1 = (fun i j => raw25875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25875step1 raw25875step0; decide +kernel
      have hl : raw25875step1Labels = raw25875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25875step0 raw25875step0Labels permutation56 hz
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw25876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25876 raw25876Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25876 raw25876Labels = mixedMoment B raw25876step0 raw25876step0Labels := by
      have hz : ∀ j, raw25876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25876step0 = (fun i j => raw25876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25876step0 raw25876; decide +kernel
      have hl : raw25876step0Labels = raw25876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25876 raw25876Labels permutation346 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw25877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25877 raw25877Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw25877 raw25877Labels = mixedMoment B raw25877step0 raw25877step0Labels := by
      have hz : ∀ j, raw25877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25877step0 = (fun i j => raw25877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25877step0 raw25877; decide +kernel
      have hl : raw25877step0Labels = raw25877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25877 raw25877Labels permutation265 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw25878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25878 raw25878Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25878 raw25878Labels = mixedMoment B raw25878step0 raw25878step0Labels := by
      have hz : ∀ j, raw25878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25878step0 = (fun i j => raw25878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25878step0 raw25878; decide +kernel
      have hl : raw25878step0Labels = raw25878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25878 raw25878Labels permutation346 hz
    mixedMoment B raw25878step0 raw25878step0Labels = mixedMoment B raw25878step1 raw25878step1Labels := by
      have hz : ∀ j, raw25878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25878step1 = (fun i j => raw25878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25878step1 raw25878step0; decide +kernel
      have hl : raw25878step1Labels = raw25878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25878step0 raw25878step0Labels permutation56 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw25879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw25879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25879 raw25879Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25879 raw25879Labels = mixedMoment B raw25879step0 raw25879step0Labels := by
      have hz : ∀ j, raw25879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25879step0 = (fun i j => raw25879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25879step0 raw25879; decide +kernel
      have hl : raw25879step0Labels = raw25879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25879 raw25879Labels permutation346 hz
    mixedMoment B raw25879step0 raw25879step0Labels = mixedMoment B raw25879step1 raw25879step1Labels := by
      have hz : ∀ j, raw25879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25879step1 = (fun i j => raw25879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25879step1 raw25879step0; decide +kernel
      have hl : raw25879step1Labels = raw25879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25879step0 raw25879step0Labels permutation56 hz
    mixedMoment B raw25879step1 raw25879step1Labels = mixedMoment B raw25879step2 raw25879step2Labels := by
      have ha : raw25879step2 = (fun i j => raw25879step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25879step2 raw25879step1; decide +kernel
      have hl : raw25879step2Labels = raw25879step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25879step1 raw25879step1Labels permutation9 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw25880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25880 raw25880Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw25880 raw25880Labels = mixedMoment B raw25880step0 raw25880step0Labels := by
      have hz : ∀ j, raw25880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25880step0 = (fun i j => raw25880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25880step0 raw25880; decide +kernel
      have hl : raw25880step0Labels = raw25880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25880 raw25880Labels permutation346 hz
    mixedMoment B raw25880step0 raw25880step0Labels = mixedMoment B raw25880step1 raw25880step1Labels := by
      have hz : ∀ j, raw25880step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25880step1 = (fun i j => raw25880step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25880step1 raw25880step0; decide +kernel
      have hl : raw25880step1Labels = raw25880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25880step0 raw25880step0Labels permutation56 hz
    _ = mixedMoment B node4183 node4183Labels := by rfl

def raw25881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25881 raw25881Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw25881 raw25881Labels = mixedMoment B raw25881step0 raw25881step0Labels := by
      have hz : ∀ j, raw25881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25881step0 = (fun i j => raw25881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25881step0 raw25881; decide +kernel
      have hl : raw25881step0Labels = raw25881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25881 raw25881Labels permutation346 hz
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw25882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25882 raw25882Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw25882 raw25882Labels = mixedMoment B raw25882step0 raw25882step0Labels := by
      have hz : ∀ j, raw25882 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25882step0 = (fun i j => raw25882 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25882step0 raw25882; decide +kernel
      have hl : raw25882step0Labels = raw25882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25882 raw25882Labels permutation265 hz
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw25883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25883 raw25883Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25883 raw25883Labels = mixedMoment B raw25883step0 raw25883step0Labels := by
      have hz : ∀ j, raw25883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25883step0 = (fun i j => raw25883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25883step0 raw25883; decide +kernel
      have hl : raw25883step0Labels = raw25883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25883 raw25883Labels permutation346 hz
    mixedMoment B raw25883step0 raw25883step0Labels = mixedMoment B raw25883step1 raw25883step1Labels := by
      have hz : ∀ j, raw25883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25883step1 = (fun i j => raw25883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25883step1 raw25883step0; decide +kernel
      have hl : raw25883step1Labels = raw25883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25883step0 raw25883step0Labels permutation56 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw25884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25884 raw25884Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25884 raw25884Labels = mixedMoment B raw25884step0 raw25884step0Labels := by
      have hz : ∀ j, raw25884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25884step0 = (fun i j => raw25884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25884step0 raw25884; decide +kernel
      have hl : raw25884step0Labels = raw25884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25884 raw25884Labels permutation346 hz
    mixedMoment B raw25884step0 raw25884step0Labels = mixedMoment B raw25884step1 raw25884step1Labels := by
      have hz : ∀ j, raw25884step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25884step1 = (fun i j => raw25884step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25884step1 raw25884step0; decide +kernel
      have hl : raw25884step1Labels = raw25884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25884step0 raw25884step0Labels permutation56 hz
    mixedMoment B raw25884step1 raw25884step1Labels = mixedMoment B raw25884step2 raw25884step2Labels := by
      have ha : raw25884step2 = (fun i j => raw25884step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25884step2 raw25884step1; decide +kernel
      have hl : raw25884step2Labels = raw25884step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25884step1 raw25884step1Labels permutation10 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw25885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25885 raw25885Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw25885 raw25885Labels = mixedMoment B raw25885step0 raw25885step0Labels := by
      have hz : ∀ j, raw25885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25885step0 = (fun i j => raw25885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25885step0 raw25885; decide +kernel
      have hl : raw25885step0Labels = raw25885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25885 raw25885Labels permutation346 hz
    mixedMoment B raw25885step0 raw25885step0Labels = mixedMoment B raw25885step1 raw25885step1Labels := by
      have ha : raw25885step1 = (fun i j => raw25885step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25885step1 raw25885step0; decide +kernel
      have hl : raw25885step1Labels = raw25885step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25885step0 raw25885step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw25886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25886 raw25886Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw25886 raw25886Labels = mixedMoment B raw25886step0 raw25886step0Labels := by
      have hz : ∀ j, raw25886 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25886step0 = (fun i j => raw25886 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25886step0 raw25886; decide +kernel
      have hl : raw25886step0Labels = raw25886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25886 raw25886Labels permutation265 hz
    mixedMoment B raw25886step0 raw25886step0Labels = mixedMoment B raw25886step1 raw25886step1Labels := by
      have ha : raw25886step1 = (fun i j => raw25886step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25886step1 raw25886step0; decide +kernel
      have hl : raw25886step1Labels = raw25886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25886step0 raw25886step0Labels permutation34 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw25887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25887 raw25887Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw25887 raw25887Labels = mixedMoment B raw25887step0 raw25887step0Labels := by
      have hz : ∀ j, raw25887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25887step0 = (fun i j => raw25887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25887step0 raw25887; decide +kernel
      have hl : raw25887step0Labels = raw25887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25887 raw25887Labels permutation346 hz
    mixedMoment B raw25887step0 raw25887step0Labels = mixedMoment B raw25887step1 raw25887step1Labels := by
      have hz : ∀ j, raw25887step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25887step1 = (fun i j => raw25887step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25887step1 raw25887step0; decide +kernel
      have hl : raw25887step1Labels = raw25887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25887step0 raw25887step0Labels permutation56 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw25888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![2, 0, -2]]
def raw25888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25888step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw25888step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw25888step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25888 raw25888Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw25888 raw25888Labels = mixedMoment B raw25888step0 raw25888step0Labels := by
      have hz : ∀ j, raw25888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25888step0 = (fun i j => raw25888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25888step0 raw25888; decide +kernel
      have hl : raw25888step0Labels = raw25888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888 raw25888Labels permutation520 hz
    mixedMoment B raw25888step0 raw25888step0Labels = mixedMoment B raw25888step1 raw25888step1Labels := by
      have hz : ∀ j, raw25888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25888step1 = (fun i j => raw25888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25888step1 raw25888step0; decide +kernel
      have hl : raw25888step1Labels = raw25888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888step0 raw25888step0Labels permutation80 hz
    mixedMoment B raw25888step1 raw25888step1Labels = mixedMoment B raw25888step2 raw25888step2Labels := by
      have hz : ∀ j, raw25888step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25888step2 = (fun i j => raw25888step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25888step2 raw25888step1; decide +kernel
      have hl : raw25888step2Labels = raw25888step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25888step1 raw25888step1Labels permutation14 hz
    mixedMoment B raw25888step2 raw25888step2Labels = mixedMoment B raw25888step3 raw25888step3Labels := by
      have hz : ∀ i, raw25888step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw25888step3 = (fun i j => raw25888step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw25888step3 raw25888step2; decide +kernel
      have hl : raw25888step3Labels = (fun j => raw25888step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw25888step2 raw25888step2Labels permutation4 hz
    mixedMoment B raw25888step3 raw25888step3Labels = mixedMoment B raw25888step4 raw25888step4Labels := by
      have ha : raw25888step4 = raw25888step3 := by apply Matrix.ext; unfold raw25888step4 raw25888step3; decide +kernel
      have hl : raw25888step3Labels = labelEmbedding2 ∘ raw25888step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25888step3 raw25888step3Labels raw25888step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw25889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25889step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25889step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25889step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25889 raw25889Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25889 raw25889Labels = mixedMoment B raw25889step0 raw25889step0Labels := by
      have hz : ∀ j, raw25889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25889step0 = (fun i j => raw25889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25889step0 raw25889; decide +kernel
      have hl : raw25889step0Labels = raw25889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25889 raw25889Labels permutation346 hz
    mixedMoment B raw25889step0 raw25889step0Labels = mixedMoment B raw25889step1 raw25889step1Labels := by
      have hz : ∀ j, raw25889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25889step1 = (fun i j => raw25889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25889step1 raw25889step0; decide +kernel
      have hl : raw25889step1Labels = raw25889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25889step0 raw25889step0Labels permutation56 hz
    mixedMoment B raw25889step1 raw25889step1Labels = mixedMoment B raw25889step2 raw25889step2Labels := by
      have ha : raw25889step2 = (fun i j => raw25889step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25889step2 raw25889step1; decide +kernel
      have hl : raw25889step2Labels = raw25889step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25889step1 raw25889step1Labels permutation10 permutation7
    mixedMoment B raw25889step2 raw25889step2Labels = mixedMoment B raw25889step3 raw25889step3Labels := by
      have ha : raw25889step3 = -raw25889step2 := by apply Matrix.ext; change ∀ i j, raw25889step3 i j = -(raw25889step2 i j); unfold raw25889step3 raw25889step2; decide +kernel
      have hl : raw25889step3Labels = raw25889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25889step3 raw25889step3Labels = mixedMoment B raw25889step4 raw25889step4Labels := by
      have ha : raw25889step4 = raw25889step3 := by apply Matrix.ext; unfold raw25889step4 raw25889step3; decide +kernel
      have hl : raw25889step3Labels = labelEmbedding10 ∘ raw25889step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25889step3 raw25889step3Labels raw25889step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25890 raw25890Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25890 raw25890Labels = mixedMoment B raw25890step0 raw25890step0Labels := by
      have hz : ∀ j, raw25890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25890step0 = (fun i j => raw25890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25890step0 raw25890; decide +kernel
      have hl : raw25890step0Labels = raw25890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25890 raw25890Labels permutation346 hz
    mixedMoment B raw25890step0 raw25890step0Labels = mixedMoment B raw25890step1 raw25890step1Labels := by
      have ha : raw25890step1 = (fun i j => raw25890step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25890step1 raw25890step0; decide +kernel
      have hl : raw25890step1Labels = raw25890step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25890step0 raw25890step0Labels permutation34 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw25891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25891 raw25891Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25891 raw25891Labels = mixedMoment B raw25891step0 raw25891step0Labels := by
      have ha : raw25891step0 = (fun i j => raw25891 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25891step0 raw25891; decide +kernel
      have hl : raw25891step0Labels = raw25891Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25891 raw25891Labels permutation178 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw25892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25892 raw25892Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25892 raw25892Labels = mixedMoment B raw25892step0 raw25892step0Labels := by
      have hz : ∀ j, raw25892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25892step0 = (fun i j => raw25892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25892step0 raw25892; decide +kernel
      have hl : raw25892step0Labels = raw25892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25892 raw25892Labels permutation346 hz
    mixedMoment B raw25892step0 raw25892step0Labels = mixedMoment B raw25892step1 raw25892step1Labels := by
      have ha : raw25892step1 = (fun i j => raw25892step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25892step1 raw25892step0; decide +kernel
      have hl : raw25892step1Labels = raw25892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25892step0 raw25892step0Labels permutation38 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw25893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25893 raw25893Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25893 raw25893Labels = mixedMoment B raw25893step0 raw25893step0Labels := by
      have hz : ∀ j, raw25893 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25893step0 = (fun i j => raw25893 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25893step0 raw25893; decide +kernel
      have hl : raw25893step0Labels = raw25893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25893 raw25893Labels permutation520 hz
    mixedMoment B raw25893step0 raw25893step0Labels = mixedMoment B raw25893step1 raw25893step1Labels := by
      have hz : ∀ j, raw25893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25893step1 = (fun i j => raw25893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25893step1 raw25893step0; decide +kernel
      have hl : raw25893step1Labels = raw25893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25893step0 raw25893step0Labels permutation80 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw25894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25894 raw25894Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25894 raw25894Labels = mixedMoment B raw25894step0 raw25894step0Labels := by
      have hz : ∀ j, raw25894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25894step0 = (fun i j => raw25894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25894step0 raw25894; decide +kernel
      have hl : raw25894step0Labels = raw25894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25894 raw25894Labels permutation346 hz
    mixedMoment B raw25894step0 raw25894step0Labels = mixedMoment B raw25894step1 raw25894step1Labels := by
      have ha : raw25894step1 = (fun i j => raw25894step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25894step1 raw25894step0; decide +kernel
      have hl : raw25894step1Labels = raw25894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25894step0 raw25894step0Labels permutation34 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25895 raw25895Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25895 raw25895Labels = mixedMoment B raw25895step0 raw25895step0Labels := by
      have hz : ∀ j, raw25895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25895step0 = (fun i j => raw25895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25895step0 raw25895; decide +kernel
      have hl : raw25895step0Labels = raw25895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25895 raw25895Labels permutation265 hz
    mixedMoment B raw25895step0 raw25895step0Labels = mixedMoment B raw25895step1 raw25895step1Labels := by
      have ha : raw25895step1 = (fun i j => raw25895step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25895step1 raw25895step0; decide +kernel
      have hl : raw25895step1Labels = raw25895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25895step0 raw25895step0Labels permutation34 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw25896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25896 raw25896Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25896 raw25896Labels = mixedMoment B raw25896step0 raw25896step0Labels := by
      have ha : raw25896step0 = (fun i j => raw25896 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25896step0 raw25896; decide +kernel
      have hl : raw25896step0Labels = raw25896Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25896 raw25896Labels permutation154 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw25897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25897 raw25897Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25897 raw25897Labels = mixedMoment B raw25897step0 raw25897step0Labels := by
      have hz : ∀ j, raw25897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25897step0 = (fun i j => raw25897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25897step0 raw25897; decide +kernel
      have hl : raw25897step0Labels = raw25897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25897 raw25897Labels permutation265 hz
    mixedMoment B raw25897step0 raw25897step0Labels = mixedMoment B raw25897step1 raw25897step1Labels := by
      have ha : raw25897step1 = (fun i j => raw25897step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25897step1 raw25897step0; decide +kernel
      have hl : raw25897step1Labels = raw25897step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25897step0 raw25897step0Labels permutation38 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw25898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25898 raw25898Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25898 raw25898Labels = mixedMoment B raw25898step0 raw25898step0Labels := by
      have hz : ∀ j, raw25898 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25898step0 = (fun i j => raw25898 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25898step0 raw25898; decide +kernel
      have hl : raw25898step0Labels = raw25898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25898 raw25898Labels permutation520 hz
    mixedMoment B raw25898step0 raw25898step0Labels = mixedMoment B raw25898step1 raw25898step1Labels := by
      have hz : ∀ j, raw25898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25898step1 = (fun i j => raw25898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25898step1 raw25898step0; decide +kernel
      have hl : raw25898step1Labels = raw25898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25898step0 raw25898step0Labels permutation56 hz
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw25899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25899 raw25899Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25899 raw25899Labels = mixedMoment B raw25899step0 raw25899step0Labels := by
      have hz : ∀ j, raw25899 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25899step0 = (fun i j => raw25899 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25899step0 raw25899; decide +kernel
      have hl : raw25899step0Labels = raw25899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25899 raw25899Labels permutation265 hz
    mixedMoment B raw25899step0 raw25899step0Labels = mixedMoment B raw25899step1 raw25899step1Labels := by
      have ha : raw25899step1 = (fun i j => raw25899step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25899step1 raw25899step0; decide +kernel
      have hl : raw25899step1Labels = raw25899step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25899step0 raw25899step0Labels permutation34 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25900 raw25900Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw25900 raw25900Labels = mixedMoment B raw25900step0 raw25900step0Labels := by
      have hz : ∀ j, raw25900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25900step0 = (fun i j => raw25900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25900step0 raw25900; decide +kernel
      have hl : raw25900step0Labels = raw25900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25900 raw25900Labels permutation346 hz
    mixedMoment B raw25900step0 raw25900step0Labels = mixedMoment B raw25900step1 raw25900step1Labels := by
      have hz : ∀ j, raw25900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25900step1 = (fun i j => raw25900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25900step1 raw25900step0; decide +kernel
      have hl : raw25900step1Labels = raw25900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25900step0 raw25900step0Labels permutation56 hz
    mixedMoment B raw25900step1 raw25900step1Labels = mixedMoment B raw25900step2 raw25900step2Labels := by
      have ha : raw25900step2 = (fun i j => raw25900step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25900step2 raw25900step1; decide +kernel
      have hl : raw25900step2Labels = raw25900step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25900step1 raw25900step1Labels permutation10 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw25901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25901 raw25901Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25901 raw25901Labels = mixedMoment B raw25901step0 raw25901step0Labels := by
      have hz : ∀ j, raw25901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25901step0 = (fun i j => raw25901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25901step0 raw25901; decide +kernel
      have hl : raw25901step0Labels = raw25901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25901 raw25901Labels permutation346 hz
    mixedMoment B raw25901step0 raw25901step0Labels = mixedMoment B raw25901step1 raw25901step1Labels := by
      have ha : raw25901step1 = (fun i j => raw25901step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25901step1 raw25901step0; decide +kernel
      have hl : raw25901step1Labels = raw25901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25901step0 raw25901step0Labels permutation34 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25902 raw25902Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25902 raw25902Labels = mixedMoment B raw25902step0 raw25902step0Labels := by
      have hz : ∀ j, raw25902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25902step0 = (fun i j => raw25902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25902step0 raw25902; decide +kernel
      have hl : raw25902step0Labels = raw25902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25902 raw25902Labels permutation265 hz
    mixedMoment B raw25902step0 raw25902step0Labels = mixedMoment B raw25902step1 raw25902step1Labels := by
      have ha : raw25902step1 = (fun i j => raw25902step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25902step1 raw25902step0; decide +kernel
      have hl : raw25902step1Labels = raw25902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25902step0 raw25902step0Labels permutation34 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw25903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25903 raw25903Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw25903 raw25903Labels = mixedMoment B raw25903step0 raw25903step0Labels := by
      have hz : ∀ j, raw25903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25903step0 = (fun i j => raw25903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25903step0 raw25903; decide +kernel
      have hl : raw25903step0Labels = raw25903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903 raw25903Labels permutation520 hz
    mixedMoment B raw25903step0 raw25903step0Labels = mixedMoment B raw25903step1 raw25903step1Labels := by
      have hz : ∀ j, raw25903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25903step1 = (fun i j => raw25903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25903step1 raw25903step0; decide +kernel
      have hl : raw25903step1Labels = raw25903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903step0 raw25903step0Labels permutation80 hz
    mixedMoment B raw25903step1 raw25903step1Labels = mixedMoment B raw25903step2 raw25903step2Labels := by
      have hz : ∀ j, raw25903step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25903step2 = (fun i j => raw25903step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25903step2 raw25903step1; decide +kernel
      have hl : raw25903step2Labels = raw25903step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25903step1 raw25903step1Labels permutation14 hz
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw25904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw25904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25904 raw25904Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25904 raw25904Labels = mixedMoment B raw25904step0 raw25904step0Labels := by
      have hz : ∀ j, raw25904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25904step0 = (fun i j => raw25904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25904step0 raw25904; decide +kernel
      have hl : raw25904step0Labels = raw25904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25904 raw25904Labels permutation346 hz
    mixedMoment B raw25904step0 raw25904step0Labels = mixedMoment B raw25904step1 raw25904step1Labels := by
      have hz : ∀ j, raw25904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25904step1 = (fun i j => raw25904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25904step1 raw25904step0; decide +kernel
      have hl : raw25904step1Labels = raw25904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25904step0 raw25904step0Labels permutation56 hz
    mixedMoment B raw25904step1 raw25904step1Labels = mixedMoment B raw25904step2 raw25904step2Labels := by
      have ha : raw25904step2 = (fun i j => raw25904step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25904step2 raw25904step1; decide +kernel
      have hl : raw25904step2Labels = raw25904step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25904step1 raw25904step1Labels permutation11 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25905 raw25905Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw25905 raw25905Labels = mixedMoment B raw25905step0 raw25905step0Labels := by
      have hz : ∀ j, raw25905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25905step0 = (fun i j => raw25905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25905step0 raw25905; decide +kernel
      have hl : raw25905step0Labels = raw25905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25905 raw25905Labels permutation346 hz
    mixedMoment B raw25905step0 raw25905step0Labels = mixedMoment B raw25905step1 raw25905step1Labels := by
      have hz : ∀ j, raw25905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25905step1 = (fun i j => raw25905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25905step1 raw25905step0; decide +kernel
      have hl : raw25905step1Labels = raw25905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25905step0 raw25905step0Labels permutation56 hz
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw25906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25906 raw25906Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25906 raw25906Labels = mixedMoment B raw25906step0 raw25906step0Labels := by
      have hz : ∀ j, raw25906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25906step0 = (fun i j => raw25906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25906step0 raw25906; decide +kernel
      have hl : raw25906step0Labels = raw25906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25906 raw25906Labels permutation346 hz
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw25907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25907 raw25907Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25907 raw25907Labels = mixedMoment B raw25907step0 raw25907step0Labels := by
      have hz : ∀ j, raw25907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25907step0 = (fun i j => raw25907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25907step0 raw25907; decide +kernel
      have hl : raw25907step0Labels = raw25907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25907 raw25907Labels permutation265 hz
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw25908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25908 raw25908Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25908 raw25908Labels = mixedMoment B raw25908step0 raw25908step0Labels := by
      have hz : ∀ j, raw25908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25908step0 = (fun i j => raw25908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25908step0 raw25908; decide +kernel
      have hl : raw25908step0Labels = raw25908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25908 raw25908Labels permutation346 hz
    mixedMoment B raw25908step0 raw25908step0Labels = mixedMoment B raw25908step1 raw25908step1Labels := by
      have hz : ∀ j, raw25908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25908step1 = (fun i j => raw25908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25908step1 raw25908step0; decide +kernel
      have hl : raw25908step1Labels = raw25908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25908step0 raw25908step0Labels permutation56 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw25909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw25909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25909step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25909 raw25909Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25909 raw25909Labels = mixedMoment B raw25909step0 raw25909step0Labels := by
      have hz : ∀ j, raw25909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25909step0 = (fun i j => raw25909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25909step0 raw25909; decide +kernel
      have hl : raw25909step0Labels = raw25909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25909 raw25909Labels permutation346 hz
    mixedMoment B raw25909step0 raw25909step0Labels = mixedMoment B raw25909step1 raw25909step1Labels := by
      have hz : ∀ j, raw25909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25909step1 = (fun i j => raw25909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25909step1 raw25909step0; decide +kernel
      have hl : raw25909step1Labels = raw25909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25909step0 raw25909step0Labels permutation56 hz
    mixedMoment B raw25909step1 raw25909step1Labels = mixedMoment B raw25909step2 raw25909step2Labels := by
      have ha : raw25909step2 = (fun i j => raw25909step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25909step2 raw25909step1; decide +kernel
      have hl : raw25909step2Labels = raw25909step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25909step1 raw25909step1Labels permutation9 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25910 raw25910Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw25910 raw25910Labels = mixedMoment B raw25910step0 raw25910step0Labels := by
      have hz : ∀ j, raw25910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25910step0 = (fun i j => raw25910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25910step0 raw25910; decide +kernel
      have hl : raw25910step0Labels = raw25910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25910 raw25910Labels permutation346 hz
    mixedMoment B raw25910step0 raw25910step0Labels = mixedMoment B raw25910step1 raw25910step1Labels := by
      have hz : ∀ j, raw25910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25910step1 = (fun i j => raw25910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25910step1 raw25910step0; decide +kernel
      have hl : raw25910step1Labels = raw25910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25910step0 raw25910step0Labels permutation56 hz
    mixedMoment B raw25910step1 raw25910step1Labels = mixedMoment B raw25910step2 raw25910step2Labels := by
      have ha : raw25910step2 = (fun i j => raw25910step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25910step2 raw25910step1; decide +kernel
      have hl : raw25910step2Labels = raw25910step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25910step1 raw25910step1Labels permutation10 permutation2
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw25911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25911 raw25911Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw25911 raw25911Labels = mixedMoment B raw25911step0 raw25911step0Labels := by
      have hz : ∀ j, raw25911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25911step0 = (fun i j => raw25911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25911step0 raw25911; decide +kernel
      have hl : raw25911step0Labels = raw25911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25911 raw25911Labels permutation346 hz
    mixedMoment B raw25911step0 raw25911step0Labels = mixedMoment B raw25911step1 raw25911step1Labels := by
      have ha : raw25911step1 = (fun i j => raw25911step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25911step1 raw25911step0; decide +kernel
      have hl : raw25911step1Labels = raw25911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25911step0 raw25911step0Labels permutation34 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw25912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25912 raw25912Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw25912 raw25912Labels = mixedMoment B raw25912step0 raw25912step0Labels := by
      have hz : ∀ j, raw25912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25912step0 = (fun i j => raw25912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25912step0 raw25912; decide +kernel
      have hl : raw25912step0Labels = raw25912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25912 raw25912Labels permutation265 hz
    mixedMoment B raw25912step0 raw25912step0Labels = mixedMoment B raw25912step1 raw25912step1Labels := by
      have ha : raw25912step1 = (fun i j => raw25912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25912step1 raw25912step0; decide +kernel
      have hl : raw25912step1Labels = raw25912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25912step0 raw25912step0Labels permutation34 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw25913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25913 raw25913Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw25913 raw25913Labels = mixedMoment B raw25913step0 raw25913step0Labels := by
      have hz : ∀ j, raw25913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25913step0 = (fun i j => raw25913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25913step0 raw25913; decide +kernel
      have hl : raw25913step0Labels = raw25913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25913 raw25913Labels permutation346 hz
    mixedMoment B raw25913step0 raw25913step0Labels = mixedMoment B raw25913step1 raw25913step1Labels := by
      have hz : ∀ j, raw25913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25913step1 = (fun i j => raw25913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25913step1 raw25913step0; decide +kernel
      have hl : raw25913step1Labels = raw25913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25913step0 raw25913step0Labels permutation56 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw25914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw25914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw25914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25914 raw25914Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw25914 raw25914Labels = mixedMoment B raw25914step0 raw25914step0Labels := by
      have hz : ∀ j, raw25914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25914step0 = (fun i j => raw25914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25914step0 raw25914; decide +kernel
      have hl : raw25914step0Labels = raw25914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914 raw25914Labels permutation520 hz
    mixedMoment B raw25914step0 raw25914step0Labels = mixedMoment B raw25914step1 raw25914step1Labels := by
      have hz : ∀ j, raw25914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25914step1 = (fun i j => raw25914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25914step1 raw25914step0; decide +kernel
      have hl : raw25914step1Labels = raw25914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914step0 raw25914step0Labels permutation80 hz
    mixedMoment B raw25914step1 raw25914step1Labels = mixedMoment B raw25914step2 raw25914step2Labels := by
      have hz : ∀ j, raw25914step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25914step2 = (fun i j => raw25914step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25914step2 raw25914step1; decide +kernel
      have hl : raw25914step2Labels = raw25914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25914step1 raw25914step1Labels permutation14 hz
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw25915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25915 raw25915Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw25915 raw25915Labels = mixedMoment B raw25915step0 raw25915step0Labels := by
      have hz : ∀ j, raw25915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25915step0 = (fun i j => raw25915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25915step0 raw25915; decide +kernel
      have hl : raw25915step0Labels = raw25915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25915 raw25915Labels permutation346 hz
    mixedMoment B raw25915step0 raw25915step0Labels = mixedMoment B raw25915step1 raw25915step1Labels := by
      have hz : ∀ j, raw25915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25915step1 = (fun i j => raw25915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25915step1 raw25915step0; decide +kernel
      have hl : raw25915step1Labels = raw25915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25915step0 raw25915step0Labels permutation56 hz
    mixedMoment B raw25915step1 raw25915step1Labels = mixedMoment B raw25915step2 raw25915step2Labels := by
      have ha : raw25915step2 = (fun i j => raw25915step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25915step2 raw25915step1; decide +kernel
      have hl : raw25915step2Labels = raw25915step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25915step1 raw25915step1Labels permutation10 permutation2
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw25916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25916 raw25916Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw25916 raw25916Labels = mixedMoment B raw25916step0 raw25916step0Labels := by
      have hz : ∀ j, raw25916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25916step0 = (fun i j => raw25916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25916step0 raw25916; decide +kernel
      have hl : raw25916step0Labels = raw25916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25916 raw25916Labels permutation346 hz
    mixedMoment B raw25916step0 raw25916step0Labels = mixedMoment B raw25916step1 raw25916step1Labels := by
      have ha : raw25916step1 = (fun i j => raw25916step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25916step1 raw25916step0; decide +kernel
      have hl : raw25916step1Labels = raw25916step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25916step0 raw25916step0Labels permutation34 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw25917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25917 raw25917Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw25917 raw25917Labels = mixedMoment B raw25917step0 raw25917step0Labels := by
      have hz : ∀ j, raw25917 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25917step0 = (fun i j => raw25917 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25917step0 raw25917; decide +kernel
      have hl : raw25917step0Labels = raw25917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25917 raw25917Labels permutation265 hz
    mixedMoment B raw25917step0 raw25917step0Labels = mixedMoment B raw25917step1 raw25917step1Labels := by
      have ha : raw25917step1 = (fun i j => raw25917step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25917step1 raw25917step0; decide +kernel
      have hl : raw25917step1Labels = raw25917step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25917step0 raw25917step0Labels permutation34 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw25918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw25918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25918 raw25918Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw25918 raw25918Labels = mixedMoment B raw25918step0 raw25918step0Labels := by
      have hz : ∀ j, raw25918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25918step0 = (fun i j => raw25918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25918step0 raw25918; decide +kernel
      have hl : raw25918step0Labels = raw25918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25918 raw25918Labels permutation346 hz
    mixedMoment B raw25918step0 raw25918step0Labels = mixedMoment B raw25918step1 raw25918step1Labels := by
      have hz : ∀ j, raw25918step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25918step1 = (fun i j => raw25918step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25918step1 raw25918step0; decide +kernel
      have hl : raw25918step1Labels = raw25918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25918step0 raw25918step0Labels permutation56 hz
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw25919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw25919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw25919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25919 raw25919Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw25919 raw25919Labels = mixedMoment B raw25919step0 raw25919step0Labels := by
      have hz : ∀ j, raw25919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25919step0 = (fun i j => raw25919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25919step0 raw25919; decide +kernel
      have hl : raw25919step0Labels = raw25919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25919 raw25919Labels permutation346 hz
    mixedMoment B raw25919step0 raw25919step0Labels = mixedMoment B raw25919step1 raw25919step1Labels := by
      have hz : ∀ j, raw25919step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25919step1 = (fun i j => raw25919step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25919step1 raw25919step0; decide +kernel
      have hl : raw25919step1Labels = raw25919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25919step0 raw25919step0Labels permutation56 hz
    mixedMoment B raw25919step1 raw25919step1Labels = mixedMoment B raw25919step2 raw25919step2Labels := by
      have ha : raw25919step2 = (fun i j => raw25919step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25919step2 raw25919step1; decide +kernel
      have hl : raw25919step2Labels = raw25919step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25919step1 raw25919step1Labels permutation10 permutation2
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw25920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw25920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25920 raw25920Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw25920 raw25920Labels = mixedMoment B raw25920step0 raw25920step0Labels := by
      have hz : ∀ j, raw25920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25920step0 = (fun i j => raw25920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25920step0 raw25920; decide +kernel
      have hl : raw25920step0Labels = raw25920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25920 raw25920Labels permutation346 hz
    mixedMoment B raw25920step0 raw25920step0Labels = mixedMoment B raw25920step1 raw25920step1Labels := by
      have hz : ∀ j, raw25920step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25920step1 = (fun i j => raw25920step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25920step1 raw25920step0; decide +kernel
      have hl : raw25920step1Labels = raw25920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25920step0 raw25920step0Labels permutation56 hz
    mixedMoment B raw25920step1 raw25920step1Labels = mixedMoment B raw25920step2 raw25920step2Labels := by
      have ha : raw25920step2 = (fun i j => raw25920step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25920step2 raw25920step1; decide +kernel
      have hl : raw25920step2Labels = raw25920step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25920step1 raw25920step1Labels permutation10 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw25921 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw25921step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw25921step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25921 raw25921Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw25921 raw25921Labels = mixedMoment B raw25921step0 raw25921step0Labels := by
      have hz : ∀ j, raw25921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25921step0 = (fun i j => raw25921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25921step0 raw25921; decide +kernel
      have hl : raw25921step0Labels = raw25921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25921 raw25921Labels permutation346 hz
    mixedMoment B raw25921step0 raw25921step0Labels = mixedMoment B raw25921step1 raw25921step1Labels := by
      have hz : ∀ j, raw25921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25921step1 = (fun i j => raw25921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25921step1 raw25921step0; decide +kernel
      have hl : raw25921step1Labels = raw25921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25921step0 raw25921step0Labels permutation56 hz
    mixedMoment B raw25921step1 raw25921step1Labels = mixedMoment B raw25921step2 raw25921step2Labels := by
      have ha : raw25921step2 = (fun i j => raw25921step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25921step2 raw25921step1; decide +kernel
      have hl : raw25921step2Labels = raw25921step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25921step1 raw25921step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw25922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25922 raw25922Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw25922 raw25922Labels = mixedMoment B raw25922step0 raw25922step0Labels := by
      have hz : ∀ j, raw25922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25922step0 = (fun i j => raw25922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25922step0 raw25922; decide +kernel
      have hl : raw25922step0Labels = raw25922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25922 raw25922Labels permutation346 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw25923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25923 raw25923Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw25923 raw25923Labels = mixedMoment B raw25923step0 raw25923step0Labels := by
      have hz : ∀ j, raw25923 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25923step0 = (fun i j => raw25923 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25923step0 raw25923; decide +kernel
      have hl : raw25923step0Labels = raw25923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25923 raw25923Labels permutation265 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw25924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25924step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25924step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25924step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25924step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25924 raw25924Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw25924 raw25924Labels = mixedMoment B raw25924step0 raw25924step0Labels := by
      have hz : ∀ j, raw25924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25924step0 = (fun i j => raw25924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25924step0 raw25924; decide +kernel
      have hl : raw25924step0Labels = raw25924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25924 raw25924Labels permutation520 hz
    mixedMoment B raw25924step0 raw25924step0Labels = mixedMoment B raw25924step1 raw25924step1Labels := by
      have hz : ∀ j, raw25924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25924step1 = (fun i j => raw25924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25924step1 raw25924step0; decide +kernel
      have hl : raw25924step1Labels = raw25924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25924step0 raw25924step0Labels permutation80 hz
    mixedMoment B raw25924step1 raw25924step1Labels = mixedMoment B raw25924step2 raw25924step2Labels := by
      have hz : ∀ j, raw25924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25924step2 = (fun i j => raw25924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25924step2 raw25924step1; decide +kernel
      have hl : raw25924step2Labels = raw25924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25924step1 raw25924step1Labels permutation14 hz
    mixedMoment B raw25924step2 raw25924step2Labels = mixedMoment B raw25924step3 raw25924step3Labels := by
      have ha : raw25924step3 = (fun i j => raw25924step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25924step3 raw25924step2; decide +kernel
      have hl : raw25924step3Labels = raw25924step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25924step2 raw25924step2Labels permutation2 permutation7
    mixedMoment B raw25924step3 raw25924step3Labels = mixedMoment B raw25924step4 raw25924step4Labels := by
      have ha : raw25924step4 = -raw25924step3 := by apply Matrix.ext; change ∀ i j, raw25924step4 i j = -(raw25924step3 i j); unfold raw25924step4 raw25924step3; decide +kernel
      have hl : raw25924step4Labels = raw25924step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25924step4 raw25924step4Labels = mixedMoment B raw25924step5 raw25924step5Labels := by
      have ha : raw25924step5 = raw25924step4 := by apply Matrix.ext; unfold raw25924step5 raw25924step4; decide +kernel
      have hl : raw25924step4Labels = labelEmbedding10 ∘ raw25924step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25924step4 raw25924step4Labels raw25924step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw25925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25925step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25925step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25925step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25925 raw25925Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw25925 raw25925Labels = mixedMoment B raw25925step0 raw25925step0Labels := by
      have hz : ∀ j, raw25925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25925step0 = (fun i j => raw25925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25925step0 raw25925; decide +kernel
      have hl : raw25925step0Labels = raw25925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25925 raw25925Labels permutation346 hz
    mixedMoment B raw25925step0 raw25925step0Labels = mixedMoment B raw25925step1 raw25925step1Labels := by
      have hz : ∀ j, raw25925step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25925step1 = (fun i j => raw25925step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25925step1 raw25925step0; decide +kernel
      have hl : raw25925step1Labels = raw25925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25925step0 raw25925step0Labels permutation56 hz
    mixedMoment B raw25925step1 raw25925step1Labels = mixedMoment B raw25925step2 raw25925step2Labels := by
      have ha : raw25925step2 = (fun i j => raw25925step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25925step2 raw25925step1; decide +kernel
      have hl : raw25925step2Labels = raw25925step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25925step1 raw25925step1Labels permutation8 permutation7
    mixedMoment B raw25925step2 raw25925step2Labels = mixedMoment B raw25925step3 raw25925step3Labels := by
      have ha : raw25925step3 = -raw25925step2 := by apply Matrix.ext; change ∀ i j, raw25925step3 i j = -(raw25925step2 i j); unfold raw25925step3 raw25925step2; decide +kernel
      have hl : raw25925step3Labels = raw25925step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25925step3 raw25925step3Labels = mixedMoment B raw25925step4 raw25925step4Labels := by
      have ha : raw25925step4 = raw25925step3 := by apply Matrix.ext; unfold raw25925step4 raw25925step3; decide +kernel
      have hl : raw25925step3Labels = labelEmbedding10 ∘ raw25925step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25925step3 raw25925step3Labels raw25925step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw25926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25926 raw25926Labels = mixedMoment B node4170 node4170Labels := by
  calc
    mixedMoment B raw25926 raw25926Labels = mixedMoment B raw25926step0 raw25926step0Labels := by
      have hz : ∀ j, raw25926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25926step0 = (fun i j => raw25926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25926step0 raw25926; decide +kernel
      have hl : raw25926step0Labels = raw25926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25926 raw25926Labels permutation346 hz
    _ = mixedMoment B node4170 node4170Labels := by rfl

def raw25927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25927 raw25927Labels = mixedMoment B node4340 node4340Labels := by
  calc
    mixedMoment B raw25927 raw25927Labels = mixedMoment B raw25927step0 raw25927step0Labels := by
      have ha : raw25927step0 = (fun i j => raw25927 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25927step0 raw25927; decide +kernel
      have hl : raw25927step0Labels = raw25927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25927 raw25927Labels permutation176 permutation2
    _ = mixedMoment B node4340 node4340Labels := by rfl

def raw25928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25928 raw25928Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw25928 raw25928Labels = mixedMoment B raw25928step0 raw25928step0Labels := by
      have hz : ∀ j, raw25928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25928step0 = (fun i j => raw25928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25928step0 raw25928; decide +kernel
      have hl : raw25928step0Labels = raw25928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25928 raw25928Labels permutation520 hz
    mixedMoment B raw25928step0 raw25928step0Labels = mixedMoment B raw25928step1 raw25928step1Labels := by
      have hz : ∀ j, raw25928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25928step1 = (fun i j => raw25928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25928step1 raw25928step0; decide +kernel
      have hl : raw25928step1Labels = raw25928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25928step0 raw25928step0Labels permutation80 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw25929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25929 raw25929Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw25929 raw25929Labels = mixedMoment B raw25929step0 raw25929step0Labels := by
      have hz : ∀ j, raw25929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25929step0 = (fun i j => raw25929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25929step0 raw25929; decide +kernel
      have hl : raw25929step0Labels = raw25929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25929 raw25929Labels permutation346 hz
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw25930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25930 raw25930Labels = mixedMoment B node4170 node4170Labels := by
  calc
    mixedMoment B raw25930 raw25930Labels = mixedMoment B raw25930step0 raw25930step0Labels := by
      have hz : ∀ j, raw25930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25930step0 = (fun i j => raw25930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25930step0 raw25930; decide +kernel
      have hl : raw25930step0Labels = raw25930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25930 raw25930Labels permutation265 hz
    _ = mixedMoment B node4170 node4170Labels := by rfl

def raw25931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25931 raw25931Labels = mixedMoment B node4340 node4340Labels := by
  calc
    _ = mixedMoment B node4340 node4340Labels := by rfl

def raw25932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25932 raw25932Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw25932 raw25932Labels = mixedMoment B raw25932step0 raw25932step0Labels := by
      have hz : ∀ j, raw25932 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25932step0 = (fun i j => raw25932 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25932step0 raw25932; decide +kernel
      have hl : raw25932step0Labels = raw25932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25932 raw25932Labels permutation520 hz
    mixedMoment B raw25932step0 raw25932step0Labels = mixedMoment B raw25932step1 raw25932step1Labels := by
      have hz : ∀ j, raw25932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25932step1 = (fun i j => raw25932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25932step1 raw25932step0; decide +kernel
      have hl : raw25932step1Labels = raw25932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25932step0 raw25932step0Labels permutation56 hz
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw25933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25933 raw25933Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw25933 raw25933Labels = mixedMoment B raw25933step0 raw25933step0Labels := by
      have hz : ∀ j, raw25933 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25933step0 = (fun i j => raw25933 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25933step0 raw25933; decide +kernel
      have hl : raw25933step0Labels = raw25933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25933 raw25933Labels permutation265 hz
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw25934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25934 raw25934Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw25934 raw25934Labels = mixedMoment B raw25934step0 raw25934step0Labels := by
      have hz : ∀ j, raw25934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25934step0 = (fun i j => raw25934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25934step0 raw25934; decide +kernel
      have hl : raw25934step0Labels = raw25934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25934 raw25934Labels permutation346 hz
    mixedMoment B raw25934step0 raw25934step0Labels = mixedMoment B raw25934step1 raw25934step1Labels := by
      have hz : ∀ j, raw25934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25934step1 = (fun i j => raw25934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25934step1 raw25934step0; decide +kernel
      have hl : raw25934step1Labels = raw25934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25934step0 raw25934step0Labels permutation56 hz
    mixedMoment B raw25934step1 raw25934step1Labels = mixedMoment B raw25934step2 raw25934step2Labels := by
      have ha : raw25934step2 = (fun i j => raw25934step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25934step2 raw25934step1; decide +kernel
      have hl : raw25934step2Labels = raw25934step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25934step1 raw25934step1Labels permutation10 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw25935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25935 raw25935Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw25935 raw25935Labels = mixedMoment B raw25935step0 raw25935step0Labels := by
      have hz : ∀ j, raw25935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25935step0 = (fun i j => raw25935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25935step0 raw25935; decide +kernel
      have hl : raw25935step0Labels = raw25935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25935 raw25935Labels permutation346 hz
    mixedMoment B raw25935step0 raw25935step0Labels = mixedMoment B raw25935step1 raw25935step1Labels := by
      have ha : raw25935step1 = (fun i j => raw25935step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25935step1 raw25935step0; decide +kernel
      have hl : raw25935step1Labels = raw25935step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25935step0 raw25935step0Labels permutation34 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw25936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25936 raw25936Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw25936 raw25936Labels = mixedMoment B raw25936step0 raw25936step0Labels := by
      have hz : ∀ j, raw25936 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25936step0 = (fun i j => raw25936 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25936step0 raw25936; decide +kernel
      have hl : raw25936step0Labels = raw25936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25936 raw25936Labels permutation265 hz
    mixedMoment B raw25936step0 raw25936step0Labels = mixedMoment B raw25936step1 raw25936step1Labels := by
      have ha : raw25936step1 = (fun i j => raw25936step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25936step1 raw25936step0; decide +kernel
      have hl : raw25936step1Labels = raw25936step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25936step0 raw25936step0Labels permutation34 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw25937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25937 raw25937Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw25937 raw25937Labels = mixedMoment B raw25937step0 raw25937step0Labels := by
      have hz : ∀ j, raw25937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25937step0 = (fun i j => raw25937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25937step0 raw25937; decide +kernel
      have hl : raw25937step0Labels = raw25937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25937 raw25937Labels permutation520 hz
    mixedMoment B raw25937step0 raw25937step0Labels = mixedMoment B raw25937step1 raw25937step1Labels := by
      have hz : ∀ j, raw25937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25937step1 = (fun i j => raw25937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25937step1 raw25937step0; decide +kernel
      have hl : raw25937step1Labels = raw25937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25937step0 raw25937step0Labels permutation80 hz
    mixedMoment B raw25937step1 raw25937step1Labels = mixedMoment B raw25937step2 raw25937step2Labels := by
      have hz : ∀ j, raw25937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25937step2 = (fun i j => raw25937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25937step2 raw25937step1; decide +kernel
      have hl : raw25937step2Labels = raw25937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25937step1 raw25937step1Labels permutation14 hz
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw25938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25938 raw25938Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw25938 raw25938Labels = mixedMoment B raw25938step0 raw25938step0Labels := by
      have hz : ∀ j, raw25938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25938step0 = (fun i j => raw25938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25938step0 raw25938; decide +kernel
      have hl : raw25938step0Labels = raw25938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25938 raw25938Labels permutation346 hz
    mixedMoment B raw25938step0 raw25938step0Labels = mixedMoment B raw25938step1 raw25938step1Labels := by
      have hz : ∀ j, raw25938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25938step1 = (fun i j => raw25938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25938step1 raw25938step0; decide +kernel
      have hl : raw25938step1Labels = raw25938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25938step0 raw25938step0Labels permutation56 hz
    mixedMoment B raw25938step1 raw25938step1Labels = mixedMoment B raw25938step2 raw25938step2Labels := by
      have ha : raw25938step2 = (fun i j => raw25938step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25938step2 raw25938step1; decide +kernel
      have hl : raw25938step2Labels = raw25938step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25938step1 raw25938step1Labels permutation11 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw25939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25939 raw25939Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw25939 raw25939Labels = mixedMoment B raw25939step0 raw25939step0Labels := by
      have hz : ∀ j, raw25939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25939step0 = (fun i j => raw25939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25939step0 raw25939; decide +kernel
      have hl : raw25939step0Labels = raw25939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25939 raw25939Labels permutation346 hz
    mixedMoment B raw25939step0 raw25939step0Labels = mixedMoment B raw25939step1 raw25939step1Labels := by
      have hz : ∀ j, raw25939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25939step1 = (fun i j => raw25939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25939step1 raw25939step0; decide +kernel
      have hl : raw25939step1Labels = raw25939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25939step0 raw25939step0Labels permutation56 hz
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw25940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25940 raw25940Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw25940 raw25940Labels = mixedMoment B raw25940step0 raw25940step0Labels := by
      have hz : ∀ j, raw25940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25940step0 = (fun i j => raw25940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25940step0 raw25940; decide +kernel
      have hl : raw25940step0Labels = raw25940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25940 raw25940Labels permutation346 hz
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw25941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25941 raw25941Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw25941 raw25941Labels = mixedMoment B raw25941step0 raw25941step0Labels := by
      have hz : ∀ j, raw25941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25941step0 = (fun i j => raw25941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25941step0 raw25941; decide +kernel
      have hl : raw25941step0Labels = raw25941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25941 raw25941Labels permutation265 hz
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw25942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw25942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25942 raw25942Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw25942 raw25942Labels = mixedMoment B raw25942step0 raw25942step0Labels := by
      have hz : ∀ j, raw25942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25942step0 = (fun i j => raw25942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25942step0 raw25942; decide +kernel
      have hl : raw25942step0Labels = raw25942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25942 raw25942Labels permutation346 hz
    mixedMoment B raw25942step0 raw25942step0Labels = mixedMoment B raw25942step1 raw25942step1Labels := by
      have hz : ∀ j, raw25942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25942step1 = (fun i j => raw25942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25942step1 raw25942step0; decide +kernel
      have hl : raw25942step1Labels = raw25942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25942step0 raw25942step0Labels permutation56 hz
    mixedMoment B raw25942step1 raw25942step1Labels = mixedMoment B raw25942step2 raw25942step2Labels := by
      have ha : raw25942step2 = (fun i j => raw25942step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25942step2 raw25942step1; decide +kernel
      have hl : raw25942step2Labels = raw25942step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25942step1 raw25942step1Labels permutation9 permutation2
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw25943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25943 raw25943Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw25943 raw25943Labels = mixedMoment B raw25943step0 raw25943step0Labels := by
      have hz : ∀ j, raw25943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25943step0 = (fun i j => raw25943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25943step0 raw25943; decide +kernel
      have hl : raw25943step0Labels = raw25943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25943 raw25943Labels permutation346 hz
    mixedMoment B raw25943step0 raw25943step0Labels = mixedMoment B raw25943step1 raw25943step1Labels := by
      have ha : raw25943step1 = (fun i j => raw25943step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25943step1 raw25943step0; decide +kernel
      have hl : raw25943step1Labels = raw25943step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25943step0 raw25943step0Labels permutation137 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw25944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25944 raw25944Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw25944 raw25944Labels = mixedMoment B raw25944step0 raw25944step0Labels := by
      have hz : ∀ j, raw25944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25944step0 = (fun i j => raw25944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25944step0 raw25944; decide +kernel
      have hl : raw25944step0Labels = raw25944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25944 raw25944Labels permutation265 hz
    mixedMoment B raw25944step0 raw25944step0Labels = mixedMoment B raw25944step1 raw25944step1Labels := by
      have ha : raw25944step1 = (fun i j => raw25944step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25944step1 raw25944step0; decide +kernel
      have hl : raw25944step1Labels = raw25944step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25944step0 raw25944step0Labels permutation137 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw25945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25945step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25945step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25945 raw25945Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw25945 raw25945Labels = mixedMoment B raw25945step0 raw25945step0Labels := by
      have hz : ∀ j, raw25945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25945step0 = (fun i j => raw25945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25945step0 raw25945; decide +kernel
      have hl : raw25945step0Labels = raw25945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25945 raw25945Labels permutation434 hz
    mixedMoment B raw25945step0 raw25945step0Labels = mixedMoment B raw25945step1 raw25945step1Labels := by
      have hz : ∀ j, raw25945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25945step1 = (fun i j => raw25945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25945step1 raw25945step0; decide +kernel
      have hl : raw25945step1Labels = raw25945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25945step0 raw25945step0Labels permutation80 hz
    mixedMoment B raw25945step1 raw25945step1Labels = mixedMoment B raw25945step2 raw25945step2Labels := by
      have hz : ∀ j, raw25945step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25945step2 = (fun i j => raw25945step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25945step2 raw25945step1; decide +kernel
      have hl : raw25945step2Labels = raw25945step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25945step1 raw25945step1Labels permutation14 hz
    mixedMoment B raw25945step2 raw25945step2Labels = mixedMoment B raw25945step3 raw25945step3Labels := by
      have ha : raw25945step3 = (fun i j => raw25945step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25945step3 raw25945step2; decide +kernel
      have hl : raw25945step3Labels = raw25945step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25945step2 raw25945step2Labels permutation7 permutation6
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw25946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25946step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25946step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw25946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25946 raw25946Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw25946 raw25946Labels = mixedMoment B raw25946step0 raw25946step0Labels := by
      have hz : ∀ j, raw25946 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25946step0 = (fun i j => raw25946 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25946step0 raw25946; decide +kernel
      have hl : raw25946step0Labels = raw25946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25946 raw25946Labels permutation520 hz
    mixedMoment B raw25946step0 raw25946step0Labels = mixedMoment B raw25946step1 raw25946step1Labels := by
      have hz : ∀ j, raw25946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25946step1 = (fun i j => raw25946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25946step1 raw25946step0; decide +kernel
      have hl : raw25946step1Labels = raw25946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25946step0 raw25946step0Labels permutation80 hz
    mixedMoment B raw25946step1 raw25946step1Labels = mixedMoment B raw25946step2 raw25946step2Labels := by
      have hz : ∀ j, raw25946step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25946step2 = (fun i j => raw25946step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25946step2 raw25946step1; decide +kernel
      have hl : raw25946step2Labels = raw25946step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25946step1 raw25946step1Labels permutation14 hz
    mixedMoment B raw25946step2 raw25946step2Labels = mixedMoment B raw25946step3 raw25946step3Labels := by
      have ha : raw25946step3 = (fun i j => raw25946step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25946step3 raw25946step2; decide +kernel
      have hl : raw25946step3Labels = raw25946step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25946step2 raw25946step2Labels permutation7 permutation6
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw25947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25947 raw25947Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw25947 raw25947Labels = mixedMoment B raw25947step0 raw25947step0Labels := by
      have hz : ∀ j, raw25947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25947step0 = (fun i j => raw25947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25947step0 raw25947; decide +kernel
      have hl : raw25947step0Labels = raw25947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25947 raw25947Labels permutation346 hz
    mixedMoment B raw25947step0 raw25947step0Labels = mixedMoment B raw25947step1 raw25947step1Labels := by
      have hz : ∀ j, raw25947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25947step1 = (fun i j => raw25947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25947step1 raw25947step0; decide +kernel
      have hl : raw25947step1Labels = raw25947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25947step0 raw25947step0Labels permutation56 hz
    mixedMoment B raw25947step1 raw25947step1Labels = mixedMoment B raw25947step2 raw25947step2Labels := by
      have ha : raw25947step2 = (fun i j => raw25947step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25947step2 raw25947step1; decide +kernel
      have hl : raw25947step2Labels = raw25947step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25947step1 raw25947step1Labels permutation29 permutation6
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw25948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25948 raw25948Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw25948 raw25948Labels = mixedMoment B raw25948step0 raw25948step0Labels := by
      have hz : ∀ j, raw25948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25948step0 = (fun i j => raw25948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25948step0 raw25948; decide +kernel
      have hl : raw25948step0Labels = raw25948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25948 raw25948Labels permutation346 hz
    mixedMoment B raw25948step0 raw25948step0Labels = mixedMoment B raw25948step1 raw25948step1Labels := by
      have ha : raw25948step1 = (fun i j => raw25948step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25948step1 raw25948step0; decide +kernel
      have hl : raw25948step1Labels = raw25948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25948step0 raw25948step0Labels permutation32 permutation3
    _ = mixedMoment B node651 node651Labels := by rfl

def raw25949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25949 raw25949Labels = mixedMoment B node1345 node1345Labels := by
  calc
    mixedMoment B raw25949 raw25949Labels = mixedMoment B raw25949step0 raw25949step0Labels := by
      have ha : raw25949step0 = (fun i j => raw25949 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25949step0 raw25949; decide +kernel
      have hl : raw25949step0Labels = raw25949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25949 raw25949Labels permutation176 permutation3
    _ = mixedMoment B node1345 node1345Labels := by rfl

def raw25950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25950 raw25950Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw25950 raw25950Labels = mixedMoment B raw25950step0 raw25950step0Labels := by
      have hz : ∀ j, raw25950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25950step0 = (fun i j => raw25950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25950step0 raw25950; decide +kernel
      have hl : raw25950step0Labels = raw25950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25950 raw25950Labels permutation434 hz
    mixedMoment B raw25950step0 raw25950step0Labels = mixedMoment B raw25950step1 raw25950step1Labels := by
      have hz : ∀ j, raw25950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25950step1 = (fun i j => raw25950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25950step1 raw25950step0; decide +kernel
      have hl : raw25950step1Labels = raw25950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25950step0 raw25950step0Labels permutation80 hz
    mixedMoment B raw25950step1 raw25950step1Labels = mixedMoment B raw25950step2 raw25950step2Labels := by
      have ha : raw25950step2 = (fun i j => raw25950step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25950step2 raw25950step1; decide +kernel
      have hl : raw25950step2Labels = raw25950step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25950step1 raw25950step1Labels permutation8 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw25951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25951 raw25951Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw25951 raw25951Labels = mixedMoment B raw25951step0 raw25951step0Labels := by
      have hz : ∀ j, raw25951 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25951step0 = (fun i j => raw25951 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25951step0 raw25951; decide +kernel
      have hl : raw25951step0Labels = raw25951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25951 raw25951Labels permutation520 hz
    mixedMoment B raw25951step0 raw25951step0Labels = mixedMoment B raw25951step1 raw25951step1Labels := by
      have hz : ∀ j, raw25951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25951step1 = (fun i j => raw25951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25951step1 raw25951step0; decide +kernel
      have hl : raw25951step1Labels = raw25951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25951step0 raw25951step0Labels permutation80 hz
    mixedMoment B raw25951step1 raw25951step1Labels = mixedMoment B raw25951step2 raw25951step2Labels := by
      have ha : raw25951step2 = (fun i j => raw25951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25951step2 raw25951step1; decide +kernel
      have hl : raw25951step2Labels = raw25951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25951step1 raw25951step1Labels permutation8 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw25952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25952 raw25952Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw25952 raw25952Labels = mixedMoment B raw25952step0 raw25952step0Labels := by
      have hz : ∀ j, raw25952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25952step0 = (fun i j => raw25952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25952step0 raw25952; decide +kernel
      have hl : raw25952step0Labels = raw25952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25952 raw25952Labels permutation346 hz
    mixedMoment B raw25952step0 raw25952step0Labels = mixedMoment B raw25952step1 raw25952step1Labels := by
      have ha : raw25952step1 = (fun i j => raw25952step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25952step1 raw25952step0; decide +kernel
      have hl : raw25952step1Labels = raw25952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25952step0 raw25952step0Labels permutation50 permutation3
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw25953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25953 raw25953Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw25953 raw25953Labels = mixedMoment B raw25953step0 raw25953step0Labels := by
      have hz : ∀ j, raw25953 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25953step0 = (fun i j => raw25953 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25953step0 raw25953; decide +kernel
      have hl : raw25953step0Labels = raw25953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25953 raw25953Labels permutation265 hz
    mixedMoment B raw25953step0 raw25953step0Labels = mixedMoment B raw25953step1 raw25953step1Labels := by
      have ha : raw25953step1 = (fun i j => raw25953step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25953step1 raw25953step0; decide +kernel
      have hl : raw25953step1Labels = raw25953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25953step0 raw25953step0Labels permutation32 permutation3
    _ = mixedMoment B node651 node651Labels := by rfl

def raw25954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25954 raw25954Labels = mixedMoment B node1345 node1345Labels := by
  calc
    mixedMoment B raw25954 raw25954Labels = mixedMoment B raw25954step0 raw25954step0Labels := by
      have ha : raw25954step0 = (fun i j => raw25954 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25954step0 raw25954; decide +kernel
      have hl : raw25954step0Labels = raw25954Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25954 raw25954Labels permutation152 permutation3
    _ = mixedMoment B node1345 node1345Labels := by rfl

def raw25955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25955step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25955 raw25955Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw25955 raw25955Labels = mixedMoment B raw25955step0 raw25955step0Labels := by
      have hz : ∀ j, raw25955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25955step0 = (fun i j => raw25955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25955step0 raw25955; decide +kernel
      have hl : raw25955step0Labels = raw25955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25955 raw25955Labels permutation434 hz
    mixedMoment B raw25955step0 raw25955step0Labels = mixedMoment B raw25955step1 raw25955step1Labels := by
      have hz : ∀ j, raw25955step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25955step1 = (fun i j => raw25955step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25955step1 raw25955step0; decide +kernel
      have hl : raw25955step1Labels = raw25955step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25955step0 raw25955step0Labels permutation56 hz
    mixedMoment B raw25955step1 raw25955step1Labels = mixedMoment B raw25955step2 raw25955step2Labels := by
      have ha : raw25955step2 = (fun i j => raw25955step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25955step2 raw25955step1; decide +kernel
      have hl : raw25955step2Labels = raw25955step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25955step1 raw25955step1Labels permutation8 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw25956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25956 raw25956Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw25956 raw25956Labels = mixedMoment B raw25956step0 raw25956step0Labels := by
      have hz : ∀ j, raw25956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25956step0 = (fun i j => raw25956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25956step0 raw25956; decide +kernel
      have hl : raw25956step0Labels = raw25956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25956 raw25956Labels permutation520 hz
    mixedMoment B raw25956step0 raw25956step0Labels = mixedMoment B raw25956step1 raw25956step1Labels := by
      have hz : ∀ j, raw25956step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25956step1 = (fun i j => raw25956step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25956step1 raw25956step0; decide +kernel
      have hl : raw25956step1Labels = raw25956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25956step0 raw25956step0Labels permutation56 hz
    mixedMoment B raw25956step1 raw25956step1Labels = mixedMoment B raw25956step2 raw25956step2Labels := by
      have ha : raw25956step2 = (fun i j => raw25956step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25956step2 raw25956step1; decide +kernel
      have hl : raw25956step2Labels = raw25956step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25956step1 raw25956step1Labels permutation8 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw25957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25957 raw25957Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw25957 raw25957Labels = mixedMoment B raw25957step0 raw25957step0Labels := by
      have hz : ∀ j, raw25957 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25957step0 = (fun i j => raw25957 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25957step0 raw25957; decide +kernel
      have hl : raw25957step0Labels = raw25957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25957 raw25957Labels permutation265 hz
    mixedMoment B raw25957step0 raw25957step0Labels = mixedMoment B raw25957step1 raw25957step1Labels := by
      have ha : raw25957step1 = (fun i j => raw25957step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25957step1 raw25957step0; decide +kernel
      have hl : raw25957step1Labels = raw25957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25957step0 raw25957step0Labels permutation50 permutation3
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw25958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25958 raw25958Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw25958 raw25958Labels = mixedMoment B raw25958step0 raw25958step0Labels := by
      have hz : ∀ j, raw25958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25958step0 = (fun i j => raw25958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25958step0 raw25958; decide +kernel
      have hl : raw25958step0Labels = raw25958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25958 raw25958Labels permutation346 hz
    mixedMoment B raw25958step0 raw25958step0Labels = mixedMoment B raw25958step1 raw25958step1Labels := by
      have hz : ∀ j, raw25958step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25958step1 = (fun i j => raw25958step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25958step1 raw25958step0; decide +kernel
      have hl : raw25958step1Labels = raw25958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25958step0 raw25958step0Labels permutation56 hz
    mixedMoment B raw25958step1 raw25958step1Labels = mixedMoment B raw25958step2 raw25958step2Labels := by
      have ha : raw25958step2 = (fun i j => raw25958step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25958step2 raw25958step1; decide +kernel
      have hl : raw25958step2Labels = raw25958step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25958step1 raw25958step1Labels permutation11 permutation3
    _ = mixedMoment B node653 node653Labels := by rfl

def raw25959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25959 raw25959Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw25959 raw25959Labels = mixedMoment B raw25959step0 raw25959step0Labels := by
      have hz : ∀ j, raw25959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25959step0 = (fun i j => raw25959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25959step0 raw25959; decide +kernel
      have hl : raw25959step0Labels = raw25959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25959 raw25959Labels permutation346 hz
    mixedMoment B raw25959step0 raw25959step0Labels = mixedMoment B raw25959step1 raw25959step1Labels := by
      have ha : raw25959step1 = (fun i j => raw25959step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25959step1 raw25959step0; decide +kernel
      have hl : raw25959step1Labels = raw25959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25959step0 raw25959step0Labels permutation35 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw25960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25960 raw25960Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw25960 raw25960Labels = mixedMoment B raw25960step0 raw25960step0Labels := by
      have hz : ∀ j, raw25960 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25960step0 = (fun i j => raw25960 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25960step0 raw25960; decide +kernel
      have hl : raw25960step0Labels = raw25960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25960 raw25960Labels permutation265 hz
    mixedMoment B raw25960step0 raw25960step0Labels = mixedMoment B raw25960step1 raw25960step1Labels := by
      have ha : raw25960step1 = (fun i j => raw25960step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25960step1 raw25960step0; decide +kernel
      have hl : raw25960step1Labels = raw25960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25960step0 raw25960step0Labels permutation35 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw25961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25961step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25961step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25961 raw25961Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw25961 raw25961Labels = mixedMoment B raw25961step0 raw25961step0Labels := by
      have hz : ∀ j, raw25961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25961step0 = (fun i j => raw25961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25961step0 raw25961; decide +kernel
      have hl : raw25961step0Labels = raw25961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25961 raw25961Labels permutation520 hz
    mixedMoment B raw25961step0 raw25961step0Labels = mixedMoment B raw25961step1 raw25961step1Labels := by
      have hz : ∀ j, raw25961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25961step1 = (fun i j => raw25961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25961step1 raw25961step0; decide +kernel
      have hl : raw25961step1Labels = raw25961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25961step0 raw25961step0Labels permutation80 hz
    mixedMoment B raw25961step1 raw25961step1Labels = mixedMoment B raw25961step2 raw25961step2Labels := by
      have hz : ∀ j, raw25961step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25961step2 = (fun i j => raw25961step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25961step2 raw25961step1; decide +kernel
      have hl : raw25961step2Labels = raw25961step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25961step1 raw25961step1Labels permutation14 hz
    mixedMoment B raw25961step2 raw25961step2Labels = mixedMoment B raw25961step3 raw25961step3Labels := by
      have ha : raw25961step3 = (fun i j => raw25961step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25961step3 raw25961step2; decide +kernel
      have hl : raw25961step3Labels = raw25961step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25961step2 raw25961step2Labels permutation3 permutation3
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw25962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25962 raw25962Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw25962 raw25962Labels = mixedMoment B raw25962step0 raw25962step0Labels := by
      have hz : ∀ j, raw25962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25962step0 = (fun i j => raw25962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25962step0 raw25962; decide +kernel
      have hl : raw25962step0Labels = raw25962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25962 raw25962Labels permutation346 hz
    mixedMoment B raw25962step0 raw25962step0Labels = mixedMoment B raw25962step1 raw25962step1Labels := by
      have hz : ∀ j, raw25962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25962step1 = (fun i j => raw25962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25962step1 raw25962step0; decide +kernel
      have hl : raw25962step1Labels = raw25962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25962step0 raw25962step0Labels permutation56 hz
    mixedMoment B raw25962step1 raw25962step1Labels = mixedMoment B raw25962step2 raw25962step2Labels := by
      have ha : raw25962step2 = (fun i j => raw25962step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25962step2 raw25962step1; decide +kernel
      have hl : raw25962step2Labels = raw25962step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25962step1 raw25962step1Labels permutation13 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw25963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25963 raw25963Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw25963 raw25963Labels = mixedMoment B raw25963step0 raw25963step0Labels := by
      have hz : ∀ j, raw25963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25963step0 = (fun i j => raw25963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25963step0 raw25963; decide +kernel
      have hl : raw25963step0Labels = raw25963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25963 raw25963Labels permutation346 hz
    mixedMoment B raw25963step0 raw25963step0Labels = mixedMoment B raw25963step1 raw25963step1Labels := by
      have hz : ∀ j, raw25963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25963step1 = (fun i j => raw25963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25963step1 raw25963step0; decide +kernel
      have hl : raw25963step1Labels = raw25963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25963step0 raw25963step0Labels permutation56 hz
    mixedMoment B raw25963step1 raw25963step1Labels = mixedMoment B raw25963step2 raw25963step2Labels := by
      have ha : raw25963step2 = (fun i j => raw25963step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25963step2 raw25963step1; decide +kernel
      have hl : raw25963step2Labels = raw25963step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25963step1 raw25963step1Labels permutation9 permutation3
    _ = mixedMoment B node653 node653Labels := by rfl

def raw25964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25964 raw25964Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw25964 raw25964Labels = mixedMoment B raw25964step0 raw25964step0Labels := by
      have hz : ∀ j, raw25964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25964step0 = (fun i j => raw25964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25964step0 raw25964; decide +kernel
      have hl : raw25964step0Labels = raw25964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25964 raw25964Labels permutation346 hz
    mixedMoment B raw25964step0 raw25964step0Labels = mixedMoment B raw25964step1 raw25964step1Labels := by
      have ha : raw25964step1 = (fun i j => raw25964step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25964step1 raw25964step0; decide +kernel
      have hl : raw25964step1Labels = raw25964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25964step0 raw25964step0Labels permutation33 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw25965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw25965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25965 raw25965Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw25965 raw25965Labels = mixedMoment B raw25965step0 raw25965step0Labels := by
      have hz : ∀ j, raw25965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25965step0 = (fun i j => raw25965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25965step0 raw25965; decide +kernel
      have hl : raw25965step0Labels = raw25965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25965 raw25965Labels permutation265 hz
    mixedMoment B raw25965step0 raw25965step0Labels = mixedMoment B raw25965step1 raw25965step1Labels := by
      have ha : raw25965step1 = (fun i j => raw25965step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25965step1 raw25965step0; decide +kernel
      have hl : raw25965step1Labels = raw25965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25965step0 raw25965step0Labels permutation33 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw25966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25966step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25966step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw25966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25966 raw25966Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw25966 raw25966Labels = mixedMoment B raw25966step0 raw25966step0Labels := by
      have hz : ∀ j, raw25966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25966step0 = (fun i j => raw25966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25966step0 raw25966; decide +kernel
      have hl : raw25966step0Labels = raw25966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25966 raw25966Labels permutation434 hz
    mixedMoment B raw25966step0 raw25966step0Labels = mixedMoment B raw25966step1 raw25966step1Labels := by
      have hz : ∀ j, raw25966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25966step1 = (fun i j => raw25966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25966step1 raw25966step0; decide +kernel
      have hl : raw25966step1Labels = raw25966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25966step0 raw25966step0Labels permutation80 hz
    mixedMoment B raw25966step1 raw25966step1Labels = mixedMoment B raw25966step2 raw25966step2Labels := by
      have hz : ∀ j, raw25966step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25966step2 = (fun i j => raw25966step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25966step2 raw25966step1; decide +kernel
      have hl : raw25966step2Labels = raw25966step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25966step1 raw25966step1Labels permutation14 hz
    mixedMoment B raw25966step2 raw25966step2Labels = mixedMoment B raw25966step3 raw25966step3Labels := by
      have ha : raw25966step3 = (fun i j => raw25966step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25966step3 raw25966step2; decide +kernel
      have hl : raw25966step3Labels = raw25966step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25966step2 raw25966step2Labels permutation3 permutation3
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw25967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw25967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25967 raw25967Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw25967 raw25967Labels = mixedMoment B raw25967step0 raw25967step0Labels := by
      have hz : ∀ j, raw25967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25967step0 = (fun i j => raw25967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25967step0 raw25967; decide +kernel
      have hl : raw25967step0Labels = raw25967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25967 raw25967Labels permutation346 hz
    mixedMoment B raw25967step0 raw25967step0Labels = mixedMoment B raw25967step1 raw25967step1Labels := by
      have hz : ∀ j, raw25967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25967step1 = (fun i j => raw25967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25967step1 raw25967step0; decide +kernel
      have hl : raw25967step1Labels = raw25967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25967step0 raw25967step0Labels permutation56 hz
    mixedMoment B raw25967step1 raw25967step1Labels = mixedMoment B raw25967step2 raw25967step2Labels := by
      have ha : raw25967step2 = (fun i j => raw25967step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25967step2 raw25967step1; decide +kernel
      have hl : raw25967step2Labels = raw25967step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25967step1 raw25967step1Labels permutation12 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw25968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25968 raw25968Labels = mixedMoment B node652 node652Labels := by
  calc
    mixedMoment B raw25968 raw25968Labels = mixedMoment B raw25968step0 raw25968step0Labels := by
      have hz : ∀ j, raw25968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25968step0 = (fun i j => raw25968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25968step0 raw25968; decide +kernel
      have hl : raw25968step0Labels = raw25968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25968 raw25968Labels permutation346 hz
    mixedMoment B raw25968step0 raw25968step0Labels = mixedMoment B raw25968step1 raw25968step1Labels := by
      have hz : ∀ j, raw25968step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25968step1 = (fun i j => raw25968step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25968step1 raw25968step0; decide +kernel
      have hl : raw25968step1Labels = raw25968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25968step0 raw25968step0Labels permutation56 hz
    mixedMoment B raw25968step1 raw25968step1Labels = mixedMoment B raw25968step2 raw25968step2Labels := by
      have ha : raw25968step2 = (fun i j => raw25968step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25968step2 raw25968step1; decide +kernel
      have hl : raw25968step2Labels = raw25968step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25968step1 raw25968step1Labels permutation8 permutation3
    _ = mixedMoment B node652 node652Labels := by rfl

def raw25969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25969 raw25969Labels = mixedMoment B node1346 node1346Labels := by
  calc
    mixedMoment B raw25969 raw25969Labels = mixedMoment B raw25969step0 raw25969step0Labels := by
      have hz : ∀ j, raw25969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25969step0 = (fun i j => raw25969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25969step0 raw25969; decide +kernel
      have hl : raw25969step0Labels = raw25969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25969 raw25969Labels permutation346 hz
    mixedMoment B raw25969step0 raw25969step0Labels = mixedMoment B raw25969step1 raw25969step1Labels := by
      have ha : raw25969step1 = (fun i j => raw25969step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25969step1 raw25969step0; decide +kernel
      have hl : raw25969step1Labels = raw25969step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25969step0 raw25969step0Labels permutation32 permutation3
    _ = mixedMoment B node1346 node1346Labels := by rfl

def raw25970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25970 raw25970Labels = mixedMoment B node1346 node1346Labels := by
  calc
    mixedMoment B raw25970 raw25970Labels = mixedMoment B raw25970step0 raw25970step0Labels := by
      have hz : ∀ j, raw25970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25970step0 = (fun i j => raw25970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25970step0 raw25970; decide +kernel
      have hl : raw25970step0Labels = raw25970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25970 raw25970Labels permutation265 hz
    mixedMoment B raw25970step0 raw25970step0Labels = mixedMoment B raw25970step1 raw25970step1Labels := by
      have ha : raw25970step1 = (fun i j => raw25970step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25970step1 raw25970step0; decide +kernel
      have hl : raw25970step1Labels = raw25970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25970step0 raw25970step0Labels permutation32 permutation3
    _ = mixedMoment B node1346 node1346Labels := by rfl

def raw25971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25971step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25971step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25971step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25971 raw25971Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw25971 raw25971Labels = mixedMoment B raw25971step0 raw25971step0Labels := by
      have hz : ∀ j, raw25971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25971step0 = (fun i j => raw25971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25971step0 raw25971; decide +kernel
      have hl : raw25971step0Labels = raw25971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25971 raw25971Labels permutation434 hz
    mixedMoment B raw25971step0 raw25971step0Labels = mixedMoment B raw25971step1 raw25971step1Labels := by
      have hz : ∀ j, raw25971step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25971step1 = (fun i j => raw25971step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25971step1 raw25971step0; decide +kernel
      have hl : raw25971step1Labels = raw25971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25971step0 raw25971step0Labels permutation80 hz
    mixedMoment B raw25971step1 raw25971step1Labels = mixedMoment B raw25971step2 raw25971step2Labels := by
      have hz : ∀ j, raw25971step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25971step2 = (fun i j => raw25971step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25971step2 raw25971step1; decide +kernel
      have hl : raw25971step2Labels = raw25971step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25971step1 raw25971step1Labels permutation14 hz
    mixedMoment B raw25971step2 raw25971step2Labels = mixedMoment B raw25971step3 raw25971step3Labels := by
      have ha : raw25971step3 = (fun i j => raw25971step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25971step3 raw25971step2; decide +kernel
      have hl : raw25971step3Labels = raw25971step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25971step2 raw25971step2Labels permutation2 permutation3
    _ = mixedMoment B node1452 node1452Labels := by rfl

def raw25972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw25972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw25972step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25972step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw25972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25972 raw25972Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw25972 raw25972Labels = mixedMoment B raw25972step0 raw25972step0Labels := by
      have hz : ∀ j, raw25972 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25972step0 = (fun i j => raw25972 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25972step0 raw25972; decide +kernel
      have hl : raw25972step0Labels = raw25972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25972 raw25972Labels permutation520 hz
    mixedMoment B raw25972step0 raw25972step0Labels = mixedMoment B raw25972step1 raw25972step1Labels := by
      have hz : ∀ j, raw25972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25972step1 = (fun i j => raw25972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25972step1 raw25972step0; decide +kernel
      have hl : raw25972step1Labels = raw25972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25972step0 raw25972step0Labels permutation80 hz
    mixedMoment B raw25972step1 raw25972step1Labels = mixedMoment B raw25972step2 raw25972step2Labels := by
      have hz : ∀ j, raw25972step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25972step2 = (fun i j => raw25972step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25972step2 raw25972step1; decide +kernel
      have hl : raw25972step2Labels = raw25972step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25972step1 raw25972step1Labels permutation14 hz
    mixedMoment B raw25972step2 raw25972step2Labels = mixedMoment B raw25972step3 raw25972step3Labels := by
      have ha : raw25972step3 = (fun i j => raw25972step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25972step3 raw25972step2; decide +kernel
      have hl : raw25972step3Labels = raw25972step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25972step2 raw25972step2Labels permutation2 permutation3
    _ = mixedMoment B node1452 node1452Labels := by rfl

def raw25973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25973 raw25973Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw25973 raw25973Labels = mixedMoment B raw25973step0 raw25973step0Labels := by
      have hz : ∀ j, raw25973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25973step0 = (fun i j => raw25973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25973step0 raw25973; decide +kernel
      have hl : raw25973step0Labels = raw25973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25973 raw25973Labels permutation346 hz
    mixedMoment B raw25973step0 raw25973step0Labels = mixedMoment B raw25973step1 raw25973step1Labels := by
      have ha : raw25973step1 = (fun i j => raw25973step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25973step1 raw25973step0; decide +kernel
      have hl : raw25973step1Labels = raw25973step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25973step0 raw25973step0Labels permutation32 permutation7
    mixedMoment B raw25973step1 raw25973step1Labels = mixedMoment B raw25973step2 raw25973step2Labels := by
      have ha : raw25973step2 = -raw25973step1 := by apply Matrix.ext; change ∀ i j, raw25973step2 i j = -(raw25973step1 i j); unfold raw25973step2 raw25973step1; decide +kernel
      have hl : raw25973step2Labels = raw25973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25973step2 raw25973step2Labels = mixedMoment B raw25973step3 raw25973step3Labels := by
      have ha : raw25973step3 = raw25973step2 := by apply Matrix.ext; unfold raw25973step3 raw25973step2; decide +kernel
      have hl : raw25973step2Labels = labelEmbedding1 ∘ raw25973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25973step2 raw25973step2Labels raw25973step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw25974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25974step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25974 raw25974Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw25974 raw25974Labels = mixedMoment B raw25974step0 raw25974step0Labels := by
      have hz : ∀ j, raw25974 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25974step0 = (fun i j => raw25974 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25974step0 raw25974; decide +kernel
      have hl : raw25974step0Labels = raw25974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25974 raw25974Labels permutation265 hz
    mixedMoment B raw25974step0 raw25974step0Labels = mixedMoment B raw25974step1 raw25974step1Labels := by
      have ha : raw25974step1 = (fun i j => raw25974step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25974step1 raw25974step0; decide +kernel
      have hl : raw25974step1Labels = raw25974step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25974step0 raw25974step0Labels permutation32 permutation7
    mixedMoment B raw25974step1 raw25974step1Labels = mixedMoment B raw25974step2 raw25974step2Labels := by
      have ha : raw25974step2 = -raw25974step1 := by apply Matrix.ext; change ∀ i j, raw25974step2 i j = -(raw25974step1 i j); unfold raw25974step2 raw25974step1; decide +kernel
      have hl : raw25974step2Labels = raw25974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25974step2 raw25974step2Labels = mixedMoment B raw25974step3 raw25974step3Labels := by
      have ha : raw25974step3 = raw25974step2 := by apply Matrix.ext; unfold raw25974step3 raw25974step2; decide +kernel
      have hl : raw25974step2Labels = labelEmbedding1 ∘ raw25974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25974step2 raw25974step2Labels raw25974step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw25975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25975step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw25975step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw25975step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25975step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw25975step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25975 raw25975Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw25975 raw25975Labels = mixedMoment B raw25975step0 raw25975step0Labels := by
      have hz : ∀ j, raw25975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25975step0 = (fun i j => raw25975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25975step0 raw25975; decide +kernel
      have hl : raw25975step0Labels = raw25975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975 raw25975Labels permutation520 hz
    mixedMoment B raw25975step0 raw25975step0Labels = mixedMoment B raw25975step1 raw25975step1Labels := by
      have hz : ∀ j, raw25975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25975step1 = (fun i j => raw25975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25975step1 raw25975step0; decide +kernel
      have hl : raw25975step1Labels = raw25975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975step0 raw25975step0Labels permutation80 hz
    mixedMoment B raw25975step1 raw25975step1Labels = mixedMoment B raw25975step2 raw25975step2Labels := by
      have hz : ∀ j, raw25975step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25975step2 = (fun i j => raw25975step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25975step2 raw25975step1; decide +kernel
      have hl : raw25975step2Labels = raw25975step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25975step1 raw25975step1Labels permutation14 hz
    mixedMoment B raw25975step2 raw25975step2Labels = mixedMoment B raw25975step3 raw25975step3Labels := by
      have ha : raw25975step3 = (fun i j => raw25975step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25975step3 raw25975step2; decide +kernel
      have hl : raw25975step3Labels = raw25975step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25975step2 raw25975step2Labels permutation2 permutation7
    mixedMoment B raw25975step3 raw25975step3Labels = mixedMoment B raw25975step4 raw25975step4Labels := by
      have ha : raw25975step4 = -raw25975step3 := by apply Matrix.ext; change ∀ i j, raw25975step4 i j = -(raw25975step3 i j); unfold raw25975step4 raw25975step3; decide +kernel
      have hl : raw25975step4Labels = raw25975step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25975step4 raw25975step4Labels = mixedMoment B raw25975step5 raw25975step5Labels := by
      have ha : raw25975step5 = raw25975step4 := by apply Matrix.ext; unfold raw25975step5 raw25975step4; decide +kernel
      have hl : raw25975step4Labels = labelEmbedding1 ∘ raw25975step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25975step4 raw25975step4Labels raw25975step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw25976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25976 raw25976Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw25976 raw25976Labels = mixedMoment B raw25976step0 raw25976step0Labels := by
      have hz : ∀ j, raw25976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25976step0 = (fun i j => raw25976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25976step0 raw25976; decide +kernel
      have hl : raw25976step0Labels = raw25976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25976 raw25976Labels permutation346 hz
    mixedMoment B raw25976step0 raw25976step0Labels = mixedMoment B raw25976step1 raw25976step1Labels := by
      have hz : ∀ j, raw25976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25976step1 = (fun i j => raw25976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25976step1 raw25976step0; decide +kernel
      have hl : raw25976step1Labels = raw25976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25976step0 raw25976step0Labels permutation56 hz
    mixedMoment B raw25976step1 raw25976step1Labels = mixedMoment B raw25976step2 raw25976step2Labels := by
      have ha : raw25976step2 = (fun i j => raw25976step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25976step2 raw25976step1; decide +kernel
      have hl : raw25976step2Labels = raw25976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25976step1 raw25976step1Labels permutation8 permutation7
    mixedMoment B raw25976step2 raw25976step2Labels = mixedMoment B raw25976step3 raw25976step3Labels := by
      have ha : raw25976step3 = -raw25976step2 := by apply Matrix.ext; change ∀ i j, raw25976step3 i j = -(raw25976step2 i j); unfold raw25976step3 raw25976step2; decide +kernel
      have hl : raw25976step3Labels = raw25976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25976step3 raw25976step3Labels = mixedMoment B raw25976step4 raw25976step4Labels := by
      have ha : raw25976step4 = raw25976step3 := by apply Matrix.ext; unfold raw25976step4 raw25976step3; decide +kernel
      have hl : raw25976step3Labels = labelEmbedding1 ∘ raw25976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25976step3 raw25976step3Labels raw25976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw25977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25977 raw25977Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw25977 raw25977Labels = mixedMoment B raw25977step0 raw25977step0Labels := by
      have hz : ∀ j, raw25977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25977step0 = (fun i j => raw25977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25977step0 raw25977; decide +kernel
      have hl : raw25977step0Labels = raw25977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25977 raw25977Labels permutation346 hz
    mixedMoment B raw25977step0 raw25977step0Labels = mixedMoment B raw25977step1 raw25977step1Labels := by
      have ha : raw25977step1 = (fun i j => raw25977step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25977step1 raw25977step0; decide +kernel
      have hl : raw25977step1Labels = raw25977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25977step0 raw25977step0Labels permutation32 permutation7
    mixedMoment B raw25977step1 raw25977step1Labels = mixedMoment B raw25977step2 raw25977step2Labels := by
      have ha : raw25977step2 = -raw25977step1 := by apply Matrix.ext; change ∀ i j, raw25977step2 i j = -(raw25977step1 i j); unfold raw25977step2 raw25977step1; decide +kernel
      have hl : raw25977step2Labels = raw25977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25977step2 raw25977step2Labels = mixedMoment B raw25977step3 raw25977step3Labels := by
      have ha : raw25977step3 = raw25977step2 := by apply Matrix.ext; unfold raw25977step3 raw25977step2; decide +kernel
      have hl : raw25977step2Labels = labelEmbedding1 ∘ raw25977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25977step2 raw25977step2Labels raw25977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

def raw25978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25978 raw25978Labels = mixedMoment B node1662 node1662Labels := by
  calc
    mixedMoment B raw25978 raw25978Labels = mixedMoment B raw25978step0 raw25978step0Labels := by
      have ha : raw25978step0 = (fun i j => raw25978 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25978step0 raw25978; decide +kernel
      have hl : raw25978step0Labels = raw25978Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25978 raw25978Labels permutation176 permutation7
    mixedMoment B raw25978step0 raw25978step0Labels = mixedMoment B raw25978step1 raw25978step1Labels := by
      have ha : raw25978step1 = -raw25978step0 := by apply Matrix.ext; change ∀ i j, raw25978step1 i j = -(raw25978step0 i j); unfold raw25978step1 raw25978step0; decide +kernel
      have hl : raw25978step1Labels = raw25978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25978step1 raw25978step1Labels = mixedMoment B raw25978step2 raw25978step2Labels := by
      have ha : raw25978step2 = raw25978step1 := by apply Matrix.ext; unfold raw25978step2 raw25978step1; decide +kernel
      have hl : raw25978step1Labels = labelEmbedding1 ∘ raw25978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25978step1 raw25978step1Labels raw25978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1662 node1662Labels := by rfl

def raw25979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25979step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25979step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25979 raw25979Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw25979 raw25979Labels = mixedMoment B raw25979step0 raw25979step0Labels := by
      have hz : ∀ j, raw25979 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25979step0 = (fun i j => raw25979 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25979step0 raw25979; decide +kernel
      have hl : raw25979step0Labels = raw25979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25979 raw25979Labels permutation520 hz
    mixedMoment B raw25979step0 raw25979step0Labels = mixedMoment B raw25979step1 raw25979step1Labels := by
      have hz : ∀ j, raw25979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25979step1 = (fun i j => raw25979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25979step1 raw25979step0; decide +kernel
      have hl : raw25979step1Labels = raw25979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25979step0 raw25979step0Labels permutation80 hz
    mixedMoment B raw25979step1 raw25979step1Labels = mixedMoment B raw25979step2 raw25979step2Labels := by
      have ha : raw25979step2 = (fun i j => raw25979step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25979step2 raw25979step1; decide +kernel
      have hl : raw25979step2Labels = raw25979step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25979step1 raw25979step1Labels permutation8 permutation7
    mixedMoment B raw25979step2 raw25979step2Labels = mixedMoment B raw25979step3 raw25979step3Labels := by
      have ha : raw25979step3 = -raw25979step2 := by apply Matrix.ext; change ∀ i j, raw25979step3 i j = -(raw25979step2 i j); unfold raw25979step3 raw25979step2; decide +kernel
      have hl : raw25979step3Labels = raw25979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25979step3 raw25979step3Labels = mixedMoment B raw25979step4 raw25979step4Labels := by
      have ha : raw25979step4 = raw25979step3 := by apply Matrix.ext; unfold raw25979step4 raw25979step3; decide +kernel
      have hl : raw25979step3Labels = labelEmbedding1 ∘ raw25979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25979step3 raw25979step3Labels raw25979step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw25980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25980step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25980 raw25980Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw25980 raw25980Labels = mixedMoment B raw25980step0 raw25980step0Labels := by
      have hz : ∀ j, raw25980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25980step0 = (fun i j => raw25980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25980step0 raw25980; decide +kernel
      have hl : raw25980step0Labels = raw25980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25980 raw25980Labels permutation346 hz
    mixedMoment B raw25980step0 raw25980step0Labels = mixedMoment B raw25980step1 raw25980step1Labels := by
      have ha : raw25980step1 = (fun i j => raw25980step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25980step1 raw25980step0; decide +kernel
      have hl : raw25980step1Labels = raw25980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25980step0 raw25980step0Labels permutation32 permutation7
    mixedMoment B raw25980step1 raw25980step1Labels = mixedMoment B raw25980step2 raw25980step2Labels := by
      have ha : raw25980step2 = -raw25980step1 := by apply Matrix.ext; change ∀ i j, raw25980step2 i j = -(raw25980step1 i j); unfold raw25980step2 raw25980step1; decide +kernel
      have hl : raw25980step2Labels = raw25980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25980step2 raw25980step2Labels = mixedMoment B raw25980step3 raw25980step3Labels := by
      have ha : raw25980step3 = raw25980step2 := by apply Matrix.ext; unfold raw25980step3 raw25980step2; decide +kernel
      have hl : raw25980step2Labels = labelEmbedding1 ∘ raw25980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25980step2 raw25980step2Labels raw25980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw25981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25981 raw25981Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw25981 raw25981Labels = mixedMoment B raw25981step0 raw25981step0Labels := by
      have hz : ∀ j, raw25981 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25981step0 = (fun i j => raw25981 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25981step0 raw25981; decide +kernel
      have hl : raw25981step0Labels = raw25981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25981 raw25981Labels permutation265 hz
    mixedMoment B raw25981step0 raw25981step0Labels = mixedMoment B raw25981step1 raw25981step1Labels := by
      have ha : raw25981step1 = (fun i j => raw25981step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25981step1 raw25981step0; decide +kernel
      have hl : raw25981step1Labels = raw25981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25981step0 raw25981step0Labels permutation32 permutation7
    mixedMoment B raw25981step1 raw25981step1Labels = mixedMoment B raw25981step2 raw25981step2Labels := by
      have ha : raw25981step2 = -raw25981step1 := by apply Matrix.ext; change ∀ i j, raw25981step2 i j = -(raw25981step1 i j); unfold raw25981step2 raw25981step1; decide +kernel
      have hl : raw25981step2Labels = raw25981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25981step2 raw25981step2Labels = mixedMoment B raw25981step3 raw25981step3Labels := by
      have ha : raw25981step3 = raw25981step2 := by apply Matrix.ext; unfold raw25981step3 raw25981step2; decide +kernel
      have hl : raw25981step2Labels = labelEmbedding1 ∘ raw25981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25981step2 raw25981step2Labels raw25981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1503 node1503Labels := by rfl

def raw25982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25982 raw25982Labels = mixedMoment B node1662 node1662Labels := by
  calc
    mixedMoment B raw25982 raw25982Labels = mixedMoment B raw25982step0 raw25982step0Labels := by
      have ha : raw25982step0 = (fun i j => raw25982 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25982step0 raw25982; decide +kernel
      have hl : raw25982step0Labels = raw25982Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25982 raw25982Labels permutation152 permutation7
    mixedMoment B raw25982step0 raw25982step0Labels = mixedMoment B raw25982step1 raw25982step1Labels := by
      have ha : raw25982step1 = -raw25982step0 := by apply Matrix.ext; change ∀ i j, raw25982step1 i j = -(raw25982step0 i j); unfold raw25982step1 raw25982step0; decide +kernel
      have hl : raw25982step1Labels = raw25982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25982step1 raw25982step1Labels = mixedMoment B raw25982step2 raw25982step2Labels := by
      have ha : raw25982step2 = raw25982step1 := by apply Matrix.ext; unfold raw25982step2 raw25982step1; decide +kernel
      have hl : raw25982step1Labels = labelEmbedding1 ∘ raw25982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25982step1 raw25982step1Labels raw25982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1662 node1662Labels := by rfl

def raw25983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25983step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25983step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw25983step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25983 raw25983Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw25983 raw25983Labels = mixedMoment B raw25983step0 raw25983step0Labels := by
      have hz : ∀ j, raw25983 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25983step0 = (fun i j => raw25983 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25983step0 raw25983; decide +kernel
      have hl : raw25983step0Labels = raw25983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25983 raw25983Labels permutation520 hz
    mixedMoment B raw25983step0 raw25983step0Labels = mixedMoment B raw25983step1 raw25983step1Labels := by
      have hz : ∀ j, raw25983step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25983step1 = (fun i j => raw25983step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25983step1 raw25983step0; decide +kernel
      have hl : raw25983step1Labels = raw25983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25983step0 raw25983step0Labels permutation56 hz
    mixedMoment B raw25983step1 raw25983step1Labels = mixedMoment B raw25983step2 raw25983step2Labels := by
      have ha : raw25983step2 = (fun i j => raw25983step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25983step2 raw25983step1; decide +kernel
      have hl : raw25983step2Labels = raw25983step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25983step1 raw25983step1Labels permutation8 permutation7
    mixedMoment B raw25983step2 raw25983step2Labels = mixedMoment B raw25983step3 raw25983step3Labels := by
      have ha : raw25983step3 = -raw25983step2 := by apply Matrix.ext; change ∀ i j, raw25983step3 i j = -(raw25983step2 i j); unfold raw25983step3 raw25983step2; decide +kernel
      have hl : raw25983step3Labels = raw25983step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25983step3 raw25983step3Labels = mixedMoment B raw25983step4 raw25983step4Labels := by
      have ha : raw25983step4 = raw25983step3 := by apply Matrix.ext; unfold raw25983step4 raw25983step3; decide +kernel
      have hl : raw25983step3Labels = labelEmbedding1 ∘ raw25983step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25983step3 raw25983step3Labels raw25983step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
