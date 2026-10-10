import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25728 raw25728Labels = mixedMoment B node1008 node1008Labels := by
  calc
    mixedMoment B raw25728 raw25728Labels = mixedMoment B raw25728step0 raw25728step0Labels := by
      have hz : ∀ j, raw25728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25728step0 = (fun i j => raw25728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25728step0 raw25728; decide +kernel
      have hl : raw25728step0Labels = raw25728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25728 raw25728Labels permutation346 hz
    mixedMoment B raw25728step0 raw25728step0Labels = mixedMoment B raw25728step1 raw25728step1Labels := by
      have ha : raw25728step1 = (fun i j => raw25728step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25728step1 raw25728step0; decide +kernel
      have hl : raw25728step1Labels = raw25728step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25728step0 raw25728step0Labels permutation32 permutation6
    _ = mixedMoment B node1008 node1008Labels := by rfl

def raw25729 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25729 raw25729Labels = mixedMoment B node1008 node1008Labels := by
  calc
    mixedMoment B raw25729 raw25729Labels = mixedMoment B raw25729step0 raw25729step0Labels := by
      have hz : ∀ j, raw25729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25729step0 = (fun i j => raw25729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25729step0 raw25729; decide +kernel
      have hl : raw25729step0Labels = raw25729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25729 raw25729Labels permutation265 hz
    mixedMoment B raw25729step0 raw25729step0Labels = mixedMoment B raw25729step1 raw25729step1Labels := by
      have ha : raw25729step1 = (fun i j => raw25729step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25729step1 raw25729step0; decide +kernel
      have hl : raw25729step1Labels = raw25729step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25729step0 raw25729step0Labels permutation32 permutation6
    _ = mixedMoment B node1008 node1008Labels := by rfl

def raw25730 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw25730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25730 raw25730Labels = mixedMoment B node1090 node1090Labels := by
  calc
    mixedMoment B raw25730 raw25730Labels = mixedMoment B raw25730step0 raw25730step0Labels := by
      have hz : ∀ j, raw25730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25730step0 = (fun i j => raw25730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25730step0 raw25730; decide +kernel
      have hl : raw25730step0Labels = raw25730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25730 raw25730Labels permutation346 hz
    mixedMoment B raw25730step0 raw25730step0Labels = mixedMoment B raw25730step1 raw25730step1Labels := by
      have hz : ∀ j, raw25730step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25730step1 = (fun i j => raw25730step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25730step1 raw25730step0; decide +kernel
      have hl : raw25730step1Labels = raw25730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25730step0 raw25730step0Labels permutation56 hz
    mixedMoment B raw25730step1 raw25730step1Labels = mixedMoment B raw25730step2 raw25730step2Labels := by
      have ha : raw25730step2 = (fun i j => raw25730step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25730step2 raw25730step1; decide +kernel
      have hl : raw25730step2Labels = raw25730step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25730step1 raw25730step1Labels permutation8 permutation6
    _ = mixedMoment B node1090 node1090Labels := by rfl

def raw25731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25731step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25731 raw25731Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw25731 raw25731Labels = mixedMoment B raw25731step0 raw25731step0Labels := by
      have hz : ∀ j, raw25731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25731step0 = (fun i j => raw25731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25731step0 raw25731; decide +kernel
      have hl : raw25731step0Labels = raw25731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25731 raw25731Labels permutation346 hz
    mixedMoment B raw25731step0 raw25731step0Labels = mixedMoment B raw25731step1 raw25731step1Labels := by
      have hz : ∀ j, raw25731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25731step1 = (fun i j => raw25731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25731step1 raw25731step0; decide +kernel
      have hl : raw25731step1Labels = raw25731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25731step0 raw25731step0Labels permutation56 hz
    mixedMoment B raw25731step1 raw25731step1Labels = mixedMoment B raw25731step2 raw25731step2Labels := by
      have ha : raw25731step2 = (fun i j => raw25731step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25731step2 raw25731step1; decide +kernel
      have hl : raw25731step2Labels = raw25731step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25731step1 raw25731step1Labels permutation10 permutation6
    _ = mixedMoment B node856 node856Labels := by rfl

def raw25732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25732 raw25732Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw25732 raw25732Labels = mixedMoment B raw25732step0 raw25732step0Labels := by
      have hz : ∀ j, raw25732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25732step0 = (fun i j => raw25732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25732step0 raw25732; decide +kernel
      have hl : raw25732step0Labels = raw25732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25732 raw25732Labels permutation346 hz
    mixedMoment B raw25732step0 raw25732step0Labels = mixedMoment B raw25732step1 raw25732step1Labels := by
      have ha : raw25732step1 = (fun i j => raw25732step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25732step1 raw25732step0; decide +kernel
      have hl : raw25732step1Labels = raw25732step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25732step0 raw25732step0Labels permutation34 permutation6
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw25733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25733 raw25733Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw25733 raw25733Labels = mixedMoment B raw25733step0 raw25733step0Labels := by
      have hz : ∀ j, raw25733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25733step0 = (fun i j => raw25733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25733step0 raw25733; decide +kernel
      have hl : raw25733step0Labels = raw25733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25733 raw25733Labels permutation346 hz
    mixedMoment B raw25733step0 raw25733step0Labels = mixedMoment B raw25733step1 raw25733step1Labels := by
      have ha : raw25733step1 = (fun i j => raw25733step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25733step1 raw25733step0; decide +kernel
      have hl : raw25733step1Labels = raw25733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25733step0 raw25733step0Labels permutation34 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw25734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25734 raw25734Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw25734 raw25734Labels = mixedMoment B raw25734step0 raw25734step0Labels := by
      have hz : ∀ j, raw25734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25734step0 = (fun i j => raw25734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25734step0 raw25734; decide +kernel
      have hl : raw25734step0Labels = raw25734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25734 raw25734Labels permutation265 hz
    mixedMoment B raw25734step0 raw25734step0Labels = mixedMoment B raw25734step1 raw25734step1Labels := by
      have ha : raw25734step1 = (fun i j => raw25734step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25734step1 raw25734step0; decide +kernel
      have hl : raw25734step1Labels = raw25734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25734step0 raw25734step0Labels permutation34 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw25735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25735step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25735step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25735 raw25735Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw25735 raw25735Labels = mixedMoment B raw25735step0 raw25735step0Labels := by
      have hz : ∀ j, raw25735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25735step0 = (fun i j => raw25735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25735step0 raw25735; decide +kernel
      have hl : raw25735step0Labels = raw25735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25735 raw25735Labels permutation346 hz
    mixedMoment B raw25735step0 raw25735step0Labels = mixedMoment B raw25735step1 raw25735step1Labels := by
      have hz : ∀ j, raw25735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25735step1 = (fun i j => raw25735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25735step1 raw25735step0; decide +kernel
      have hl : raw25735step1Labels = raw25735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25735step0 raw25735step0Labels permutation56 hz
    mixedMoment B raw25735step1 raw25735step1Labels = mixedMoment B raw25735step2 raw25735step2Labels := by
      have ha : raw25735step2 = (fun i j => raw25735step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25735step2 raw25735step1; decide +kernel
      have hl : raw25735step2Labels = raw25735step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25735step1 raw25735step1Labels permutation11 permutation7
    mixedMoment B raw25735step2 raw25735step2Labels = mixedMoment B raw25735step3 raw25735step3Labels := by
      have ha : raw25735step3 = -raw25735step2 := by apply Matrix.ext; change ∀ i j, raw25735step3 i j = -(raw25735step2 i j); unfold raw25735step3 raw25735step2; decide +kernel
      have hl : raw25735step3Labels = raw25735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25735step3 raw25735step3Labels = mixedMoment B raw25735step4 raw25735step4Labels := by
      have ha : raw25735step4 = raw25735step3 := by apply Matrix.ext; unfold raw25735step4 raw25735step3; decide +kernel
      have hl : raw25735step3Labels = labelEmbedding10 ∘ raw25735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25735step3 raw25735step3Labels raw25735step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw25736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25736step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25736 raw25736Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw25736 raw25736Labels = mixedMoment B raw25736step0 raw25736step0Labels := by
      have hz : ∀ j, raw25736 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25736step0 = (fun i j => raw25736 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25736step0 raw25736; decide +kernel
      have hl : raw25736step0Labels = raw25736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736 raw25736Labels permutation520 hz
    mixedMoment B raw25736step0 raw25736step0Labels = mixedMoment B raw25736step1 raw25736step1Labels := by
      have hz : ∀ j, raw25736step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25736step1 = (fun i j => raw25736step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25736step1 raw25736step0; decide +kernel
      have hl : raw25736step1Labels = raw25736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736step0 raw25736step0Labels permutation80 hz
    mixedMoment B raw25736step1 raw25736step1Labels = mixedMoment B raw25736step2 raw25736step2Labels := by
      have hz : ∀ j, raw25736step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25736step2 = (fun i j => raw25736step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25736step2 raw25736step1; decide +kernel
      have hl : raw25736step2Labels = raw25736step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25736step1 raw25736step1Labels permutation14 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw25737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25737step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25737step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25737step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25737step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25737 raw25737Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25737 raw25737Labels = mixedMoment B raw25737step0 raw25737step0Labels := by
      have hz : ∀ j, raw25737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25737step0 = (fun i j => raw25737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25737step0 raw25737; decide +kernel
      have hl : raw25737step0Labels = raw25737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25737 raw25737Labels permutation346 hz
    mixedMoment B raw25737step0 raw25737step0Labels = mixedMoment B raw25737step1 raw25737step1Labels := by
      have hz : ∀ j, raw25737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25737step1 = (fun i j => raw25737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25737step1 raw25737step0; decide +kernel
      have hl : raw25737step1Labels = raw25737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25737step0 raw25737step0Labels permutation56 hz
    mixedMoment B raw25737step1 raw25737step1Labels = mixedMoment B raw25737step2 raw25737step2Labels := by
      have ha : raw25737step2 = (fun i j => raw25737step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25737step2 raw25737step1; decide +kernel
      have hl : raw25737step2Labels = raw25737step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25737step1 raw25737step1Labels permutation11 permutation7
    mixedMoment B raw25737step2 raw25737step2Labels = mixedMoment B raw25737step3 raw25737step3Labels := by
      have ha : raw25737step3 = -raw25737step2 := by apply Matrix.ext; change ∀ i j, raw25737step3 i j = -(raw25737step2 i j); unfold raw25737step3 raw25737step2; decide +kernel
      have hl : raw25737step3Labels = raw25737step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25737step3 raw25737step3Labels = mixedMoment B raw25737step4 raw25737step4Labels := by
      have ha : raw25737step4 = raw25737step3 := by apply Matrix.ext; unfold raw25737step4 raw25737step3; decide +kernel
      have hl : raw25737step3Labels = labelEmbedding10 ∘ raw25737step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25737step3 raw25737step3Labels raw25737step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25738 raw25738Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw25738 raw25738Labels = mixedMoment B raw25738step0 raw25738step0Labels := by
      have hz : ∀ j, raw25738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25738step0 = (fun i j => raw25738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25738step0 raw25738; decide +kernel
      have hl : raw25738step0Labels = raw25738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25738 raw25738Labels permutation346 hz
    mixedMoment B raw25738step0 raw25738step0Labels = mixedMoment B raw25738step1 raw25738step1Labels := by
      have ha : raw25738step1 = (fun i j => raw25738step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25738step1 raw25738step0; decide +kernel
      have hl : raw25738step1Labels = raw25738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25738step0 raw25738step0Labels permutation34 permutation2
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw25739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25739 raw25739Labels = mixedMoment B node4342 node4342Labels := by
  calc
    mixedMoment B raw25739 raw25739Labels = mixedMoment B raw25739step0 raw25739step0Labels := by
      have ha : raw25739step0 = (fun i j => raw25739 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25739step0 raw25739; decide +kernel
      have hl : raw25739step0Labels = raw25739Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25739 raw25739Labels permutation178 permutation2
    _ = mixedMoment B node4342 node4342Labels := by rfl

def raw25740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25740 raw25740Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw25740 raw25740Labels = mixedMoment B raw25740step0 raw25740step0Labels := by
      have hz : ∀ j, raw25740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25740step0 = (fun i j => raw25740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25740step0 raw25740; decide +kernel
      have hl : raw25740step0Labels = raw25740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25740 raw25740Labels permutation346 hz
    mixedMoment B raw25740step0 raw25740step0Labels = mixedMoment B raw25740step1 raw25740step1Labels := by
      have ha : raw25740step1 = (fun i j => raw25740step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25740step1 raw25740step0; decide +kernel
      have hl : raw25740step1Labels = raw25740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25740step0 raw25740step0Labels permutation38 permutation2
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw25741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25741 raw25741Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25741 raw25741Labels = mixedMoment B raw25741step0 raw25741step0Labels := by
      have hz : ∀ j, raw25741 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25741step0 = (fun i j => raw25741 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25741step0 raw25741; decide +kernel
      have hl : raw25741step0Labels = raw25741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25741 raw25741Labels permutation520 hz
    mixedMoment B raw25741step0 raw25741step0Labels = mixedMoment B raw25741step1 raw25741step1Labels := by
      have hz : ∀ j, raw25741step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25741step1 = (fun i j => raw25741step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25741step1 raw25741step0; decide +kernel
      have hl : raw25741step1Labels = raw25741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25741step0 raw25741step0Labels permutation80 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25742 raw25742Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25742 raw25742Labels = mixedMoment B raw25742step0 raw25742step0Labels := by
      have hz : ∀ j, raw25742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25742step0 = (fun i j => raw25742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25742step0 raw25742; decide +kernel
      have hl : raw25742step0Labels = raw25742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25742 raw25742Labels permutation346 hz
    mixedMoment B raw25742step0 raw25742step0Labels = mixedMoment B raw25742step1 raw25742step1Labels := by
      have ha : raw25742step1 = (fun i j => raw25742step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25742step1 raw25742step0; decide +kernel
      have hl : raw25742step1Labels = raw25742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25742step0 raw25742step0Labels permutation35 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25743 raw25743Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw25743 raw25743Labels = mixedMoment B raw25743step0 raw25743step0Labels := by
      have hz : ∀ j, raw25743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25743step0 = (fun i j => raw25743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25743step0 raw25743; decide +kernel
      have hl : raw25743step0Labels = raw25743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25743 raw25743Labels permutation265 hz
    mixedMoment B raw25743step0 raw25743step0Labels = mixedMoment B raw25743step1 raw25743step1Labels := by
      have ha : raw25743step1 = (fun i j => raw25743step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25743step1 raw25743step0; decide +kernel
      have hl : raw25743step1Labels = raw25743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25743step0 raw25743step0Labels permutation34 permutation2
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw25744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25744 raw25744Labels = mixedMoment B node4342 node4342Labels := by
  calc
    mixedMoment B raw25744 raw25744Labels = mixedMoment B raw25744step0 raw25744step0Labels := by
      have ha : raw25744step0 = (fun i j => raw25744 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25744step0 raw25744; decide +kernel
      have hl : raw25744step0Labels = raw25744Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25744 raw25744Labels permutation154 permutation2
    _ = mixedMoment B node4342 node4342Labels := by rfl

def raw25745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25745 raw25745Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw25745 raw25745Labels = mixedMoment B raw25745step0 raw25745step0Labels := by
      have hz : ∀ j, raw25745 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25745step0 = (fun i j => raw25745 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25745step0 raw25745; decide +kernel
      have hl : raw25745step0Labels = raw25745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25745 raw25745Labels permutation265 hz
    mixedMoment B raw25745step0 raw25745step0Labels = mixedMoment B raw25745step1 raw25745step1Labels := by
      have ha : raw25745step1 = (fun i j => raw25745step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25745step1 raw25745step0; decide +kernel
      have hl : raw25745step1Labels = raw25745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25745step0 raw25745step0Labels permutation38 permutation2
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw25746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25746 raw25746Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25746 raw25746Labels = mixedMoment B raw25746step0 raw25746step0Labels := by
      have hz : ∀ j, raw25746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25746step0 = (fun i j => raw25746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25746step0 raw25746; decide +kernel
      have hl : raw25746step0Labels = raw25746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25746 raw25746Labels permutation520 hz
    mixedMoment B raw25746step0 raw25746step0Labels = mixedMoment B raw25746step1 raw25746step1Labels := by
      have hz : ∀ j, raw25746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25746step1 = (fun i j => raw25746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25746step1 raw25746step0; decide +kernel
      have hl : raw25746step1Labels = raw25746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25746step0 raw25746step0Labels permutation56 hz
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25747 raw25747Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25747 raw25747Labels = mixedMoment B raw25747step0 raw25747step0Labels := by
      have hz : ∀ j, raw25747 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25747step0 = (fun i j => raw25747 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25747step0 raw25747; decide +kernel
      have hl : raw25747step0Labels = raw25747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25747 raw25747Labels permutation265 hz
    mixedMoment B raw25747step0 raw25747step0Labels = mixedMoment B raw25747step1 raw25747step1Labels := by
      have ha : raw25747step1 = (fun i j => raw25747step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25747step1 raw25747step0; decide +kernel
      have hl : raw25747step1Labels = raw25747step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25747step0 raw25747step0Labels permutation35 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25748 raw25748Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw25748 raw25748Labels = mixedMoment B raw25748step0 raw25748step0Labels := by
      have hz : ∀ j, raw25748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25748step0 = (fun i j => raw25748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25748step0 raw25748; decide +kernel
      have hl : raw25748step0Labels = raw25748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25748 raw25748Labels permutation346 hz
    mixedMoment B raw25748step0 raw25748step0Labels = mixedMoment B raw25748step1 raw25748step1Labels := by
      have hz : ∀ j, raw25748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25748step1 = (fun i j => raw25748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25748step1 raw25748step0; decide +kernel
      have hl : raw25748step1Labels = raw25748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25748step0 raw25748step0Labels permutation56 hz
    mixedMoment B raw25748step1 raw25748step1Labels = mixedMoment B raw25748step2 raw25748step2Labels := by
      have ha : raw25748step2 = (fun i j => raw25748step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25748step2 raw25748step1; decide +kernel
      have hl : raw25748step2Labels = raw25748step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25748step1 raw25748step1Labels permutation11 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw25749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25749 raw25749Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25749 raw25749Labels = mixedMoment B raw25749step0 raw25749step0Labels := by
      have hz : ∀ j, raw25749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25749step0 = (fun i j => raw25749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25749step0 raw25749; decide +kernel
      have hl : raw25749step0Labels = raw25749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25749 raw25749Labels permutation346 hz
    mixedMoment B raw25749step0 raw25749step0Labels = mixedMoment B raw25749step1 raw25749step1Labels := by
      have ha : raw25749step1 = (fun i j => raw25749step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25749step1 raw25749step0; decide +kernel
      have hl : raw25749step1Labels = raw25749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25749step0 raw25749step0Labels permutation35 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25750 raw25750Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25750 raw25750Labels = mixedMoment B raw25750step0 raw25750step0Labels := by
      have hz : ∀ j, raw25750 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25750step0 = (fun i j => raw25750 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25750step0 raw25750; decide +kernel
      have hl : raw25750step0Labels = raw25750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25750 raw25750Labels permutation265 hz
    mixedMoment B raw25750step0 raw25750step0Labels = mixedMoment B raw25750step1 raw25750step1Labels := by
      have ha : raw25750step1 = (fun i j => raw25750step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25750step1 raw25750step0; decide +kernel
      have hl : raw25750step1Labels = raw25750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25750step0 raw25750step0Labels permutation35 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25751step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw25751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25751 raw25751Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw25751 raw25751Labels = mixedMoment B raw25751step0 raw25751step0Labels := by
      have hz : ∀ j, raw25751 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25751step0 = (fun i j => raw25751 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25751step0 raw25751; decide +kernel
      have hl : raw25751step0Labels = raw25751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751 raw25751Labels permutation520 hz
    mixedMoment B raw25751step0 raw25751step0Labels = mixedMoment B raw25751step1 raw25751step1Labels := by
      have hz : ∀ j, raw25751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25751step1 = (fun i j => raw25751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25751step1 raw25751step0; decide +kernel
      have hl : raw25751step1Labels = raw25751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751step0 raw25751step0Labels permutation80 hz
    mixedMoment B raw25751step1 raw25751step1Labels = mixedMoment B raw25751step2 raw25751step2Labels := by
      have hz : ∀ j, raw25751step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25751step2 = (fun i j => raw25751step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25751step2 raw25751step1; decide +kernel
      have hl : raw25751step2Labels = raw25751step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25751step1 raw25751step1Labels permutation14 hz
    mixedMoment B raw25751step2 raw25751step2Labels = mixedMoment B raw25751step3 raw25751step3Labels := by
      have ha : raw25751step3 = (fun i j => raw25751step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25751step3 raw25751step2; decide +kernel
      have hl : raw25751step3Labels = raw25751step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25751step2 raw25751step2Labels permutation3 permutation2
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw25752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25752 raw25752Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25752 raw25752Labels = mixedMoment B raw25752step0 raw25752step0Labels := by
      have hz : ∀ j, raw25752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25752step0 = (fun i j => raw25752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25752step0 raw25752; decide +kernel
      have hl : raw25752step0Labels = raw25752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25752 raw25752Labels permutation346 hz
    mixedMoment B raw25752step0 raw25752step0Labels = mixedMoment B raw25752step1 raw25752step1Labels := by
      have hz : ∀ j, raw25752step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25752step1 = (fun i j => raw25752step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25752step1 raw25752step0; decide +kernel
      have hl : raw25752step1Labels = raw25752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25752step0 raw25752step0Labels permutation56 hz
    mixedMoment B raw25752step1 raw25752step1Labels = mixedMoment B raw25752step2 raw25752step2Labels := by
      have ha : raw25752step2 = (fun i j => raw25752step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25752step2 raw25752step1; decide +kernel
      have hl : raw25752step2Labels = raw25752step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25752step1 raw25752step1Labels permutation11 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw25753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25753 raw25753Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw25753 raw25753Labels = mixedMoment B raw25753step0 raw25753step0Labels := by
      have hz : ∀ j, raw25753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25753step0 = (fun i j => raw25753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25753step0 raw25753; decide +kernel
      have hl : raw25753step0Labels = raw25753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25753 raw25753Labels permutation346 hz
    mixedMoment B raw25753step0 raw25753step0Labels = mixedMoment B raw25753step1 raw25753step1Labels := by
      have hz : ∀ j, raw25753step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25753step1 = (fun i j => raw25753step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25753step1 raw25753step0; decide +kernel
      have hl : raw25753step1Labels = raw25753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25753step0 raw25753step0Labels permutation56 hz
    _ = mixedMoment B node4188 node4188Labels := by rfl

def raw25754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25754 raw25754Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25754 raw25754Labels = mixedMoment B raw25754step0 raw25754step0Labels := by
      have hz : ∀ j, raw25754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25754step0 = (fun i j => raw25754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25754step0 raw25754; decide +kernel
      have hl : raw25754step0Labels = raw25754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25754 raw25754Labels permutation346 hz
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw25755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25755 raw25755Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw25755 raw25755Labels = mixedMoment B raw25755step0 raw25755step0Labels := by
      have hz : ∀ j, raw25755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25755step0 = (fun i j => raw25755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25755step0 raw25755; decide +kernel
      have hl : raw25755step0Labels = raw25755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25755 raw25755Labels permutation265 hz
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw25756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25756 raw25756Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw25756 raw25756Labels = mixedMoment B raw25756step0 raw25756step0Labels := by
      have hz : ∀ j, raw25756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25756step0 = (fun i j => raw25756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25756step0 raw25756; decide +kernel
      have hl : raw25756step0Labels = raw25756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25756 raw25756Labels permutation346 hz
    mixedMoment B raw25756step0 raw25756step0Labels = mixedMoment B raw25756step1 raw25756step1Labels := by
      have hz : ∀ j, raw25756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25756step1 = (fun i j => raw25756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25756step1 raw25756step0; decide +kernel
      have hl : raw25756step1Labels = raw25756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25756step0 raw25756step0Labels permutation56 hz
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw25757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25757 raw25757Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25757 raw25757Labels = mixedMoment B raw25757step0 raw25757step0Labels := by
      have hz : ∀ j, raw25757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25757step0 = (fun i j => raw25757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25757step0 raw25757; decide +kernel
      have hl : raw25757step0Labels = raw25757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25757 raw25757Labels permutation346 hz
    mixedMoment B raw25757step0 raw25757step0Labels = mixedMoment B raw25757step1 raw25757step1Labels := by
      have hz : ∀ j, raw25757step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25757step1 = (fun i j => raw25757step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25757step1 raw25757step0; decide +kernel
      have hl : raw25757step1Labels = raw25757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25757step0 raw25757step0Labels permutation56 hz
    mixedMoment B raw25757step1 raw25757step1Labels = mixedMoment B raw25757step2 raw25757step2Labels := by
      have ha : raw25757step2 = (fun i j => raw25757step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25757step2 raw25757step1; decide +kernel
      have hl : raw25757step2Labels = raw25757step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25757step1 raw25757step1Labels permutation12 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25758 raw25758Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw25758 raw25758Labels = mixedMoment B raw25758step0 raw25758step0Labels := by
      have hz : ∀ j, raw25758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25758step0 = (fun i j => raw25758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25758step0 raw25758; decide +kernel
      have hl : raw25758step0Labels = raw25758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25758 raw25758Labels permutation346 hz
    mixedMoment B raw25758step0 raw25758step0Labels = mixedMoment B raw25758step1 raw25758step1Labels := by
      have hz : ∀ j, raw25758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25758step1 = (fun i j => raw25758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25758step1 raw25758step0; decide +kernel
      have hl : raw25758step1Labels = raw25758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25758step0 raw25758step0Labels permutation56 hz
    mixedMoment B raw25758step1 raw25758step1Labels = mixedMoment B raw25758step2 raw25758step2Labels := by
      have ha : raw25758step2 = (fun i j => raw25758step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25758step2 raw25758step1; decide +kernel
      have hl : raw25758step2Labels = raw25758step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25758step1 raw25758step1Labels permutation10 permutation2
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw25759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25759 raw25759Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw25759 raw25759Labels = mixedMoment B raw25759step0 raw25759step0Labels := by
      have hz : ∀ j, raw25759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25759step0 = (fun i j => raw25759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25759step0 raw25759; decide +kernel
      have hl : raw25759step0Labels = raw25759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25759 raw25759Labels permutation346 hz
    mixedMoment B raw25759step0 raw25759step0Labels = mixedMoment B raw25759step1 raw25759step1Labels := by
      have ha : raw25759step1 = (fun i j => raw25759step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25759step1 raw25759step0; decide +kernel
      have hl : raw25759step1Labels = raw25759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25759step0 raw25759step0Labels permutation34 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw25760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25760 raw25760Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw25760 raw25760Labels = mixedMoment B raw25760step0 raw25760step0Labels := by
      have hz : ∀ j, raw25760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25760step0 = (fun i j => raw25760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25760step0 raw25760; decide +kernel
      have hl : raw25760step0Labels = raw25760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25760 raw25760Labels permutation265 hz
    mixedMoment B raw25760step0 raw25760step0Labels = mixedMoment B raw25760step1 raw25760step1Labels := by
      have ha : raw25760step1 = (fun i j => raw25760step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25760step1 raw25760step0; decide +kernel
      have hl : raw25760step1Labels = raw25760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25760step0 raw25760step0Labels permutation34 permutation2
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw25761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25761 raw25761Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw25761 raw25761Labels = mixedMoment B raw25761step0 raw25761step0Labels := by
      have hz : ∀ j, raw25761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25761step0 = (fun i j => raw25761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25761step0 raw25761; decide +kernel
      have hl : raw25761step0Labels = raw25761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25761 raw25761Labels permutation346 hz
    mixedMoment B raw25761step0 raw25761step0Labels = mixedMoment B raw25761step1 raw25761step1Labels := by
      have hz : ∀ j, raw25761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25761step1 = (fun i j => raw25761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25761step1 raw25761step0; decide +kernel
      have hl : raw25761step1Labels = raw25761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25761step0 raw25761step0Labels permutation56 hz
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw25762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25762step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25762 raw25762Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw25762 raw25762Labels = mixedMoment B raw25762step0 raw25762step0Labels := by
      have hz : ∀ j, raw25762 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25762step0 = (fun i j => raw25762 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25762step0 raw25762; decide +kernel
      have hl : raw25762step0Labels = raw25762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762 raw25762Labels permutation520 hz
    mixedMoment B raw25762step0 raw25762step0Labels = mixedMoment B raw25762step1 raw25762step1Labels := by
      have hz : ∀ j, raw25762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25762step1 = (fun i j => raw25762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25762step1 raw25762step0; decide +kernel
      have hl : raw25762step1Labels = raw25762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762step0 raw25762step0Labels permutation80 hz
    mixedMoment B raw25762step1 raw25762step1Labels = mixedMoment B raw25762step2 raw25762step2Labels := by
      have hz : ∀ j, raw25762step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25762step2 = (fun i j => raw25762step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25762step2 raw25762step1; decide +kernel
      have hl : raw25762step2Labels = raw25762step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25762step1 raw25762step1Labels permutation14 hz
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw25763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25763 raw25763Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25763 raw25763Labels = mixedMoment B raw25763step0 raw25763step0Labels := by
      have hz : ∀ j, raw25763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25763step0 = (fun i j => raw25763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25763step0 raw25763; decide +kernel
      have hl : raw25763step0Labels = raw25763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25763 raw25763Labels permutation346 hz
    mixedMoment B raw25763step0 raw25763step0Labels = mixedMoment B raw25763step1 raw25763step1Labels := by
      have ha : raw25763step1 = (fun i j => raw25763step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25763step1 raw25763step0; decide +kernel
      have hl : raw25763step1Labels = raw25763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25763step0 raw25763step0Labels permutation35 permutation7
    mixedMoment B raw25763step1 raw25763step1Labels = mixedMoment B raw25763step2 raw25763step2Labels := by
      have ha : raw25763step2 = -raw25763step1 := by apply Matrix.ext; change ∀ i j, raw25763step2 i j = -(raw25763step1 i j); unfold raw25763step2 raw25763step1; decide +kernel
      have hl : raw25763step2Labels = raw25763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25763step2 raw25763step2Labels = mixedMoment B raw25763step3 raw25763step3Labels := by
      have ha : raw25763step3 = raw25763step2 := by apply Matrix.ext; unfold raw25763step3 raw25763step2; decide +kernel
      have hl : raw25763step2Labels = labelEmbedding1 ∘ raw25763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25763step2 raw25763step2Labels raw25763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw25764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25764 raw25764Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25764 raw25764Labels = mixedMoment B raw25764step0 raw25764step0Labels := by
      have hz : ∀ j, raw25764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25764step0 = (fun i j => raw25764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25764step0 raw25764; decide +kernel
      have hl : raw25764step0Labels = raw25764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25764 raw25764Labels permutation265 hz
    mixedMoment B raw25764step0 raw25764step0Labels = mixedMoment B raw25764step1 raw25764step1Labels := by
      have ha : raw25764step1 = (fun i j => raw25764step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25764step1 raw25764step0; decide +kernel
      have hl : raw25764step1Labels = raw25764step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25764step0 raw25764step0Labels permutation35 permutation7
    mixedMoment B raw25764step1 raw25764step1Labels = mixedMoment B raw25764step2 raw25764step2Labels := by
      have ha : raw25764step2 = -raw25764step1 := by apply Matrix.ext; change ∀ i j, raw25764step2 i j = -(raw25764step1 i j); unfold raw25764step2 raw25764step1; decide +kernel
      have hl : raw25764step2Labels = raw25764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25764step2 raw25764step2Labels = mixedMoment B raw25764step3 raw25764step3Labels := by
      have ha : raw25764step3 = raw25764step2 := by apply Matrix.ext; unfold raw25764step3 raw25764step2; decide +kernel
      have hl : raw25764step2Labels = labelEmbedding1 ∘ raw25764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25764step2 raw25764step2Labels raw25764step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw25765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25765 raw25765Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw25765 raw25765Labels = mixedMoment B raw25765step0 raw25765step0Labels := by
      have hz : ∀ j, raw25765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25765step0 = (fun i j => raw25765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25765step0 raw25765; decide +kernel
      have hl : raw25765step0Labels = raw25765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25765 raw25765Labels permutation346 hz
    mixedMoment B raw25765step0 raw25765step0Labels = mixedMoment B raw25765step1 raw25765step1Labels := by
      have hz : ∀ j, raw25765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25765step1 = (fun i j => raw25765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25765step1 raw25765step0; decide +kernel
      have hl : raw25765step1Labels = raw25765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25765step0 raw25765step0Labels permutation56 hz
    mixedMoment B raw25765step1 raw25765step1Labels = mixedMoment B raw25765step2 raw25765step2Labels := by
      have ha : raw25765step2 = (fun i j => raw25765step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25765step2 raw25765step1; decide +kernel
      have hl : raw25765step2Labels = raw25765step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25765step1 raw25765step1Labels permutation11 permutation7
    mixedMoment B raw25765step2 raw25765step2Labels = mixedMoment B raw25765step3 raw25765step3Labels := by
      have ha : raw25765step3 = -raw25765step2 := by apply Matrix.ext; change ∀ i j, raw25765step3 i j = -(raw25765step2 i j); unfold raw25765step3 raw25765step2; decide +kernel
      have hl : raw25765step3Labels = raw25765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25765step3 raw25765step3Labels = mixedMoment B raw25765step4 raw25765step4Labels := by
      have ha : raw25765step4 = raw25765step3 := by apply Matrix.ext; unfold raw25765step4 raw25765step3; decide +kernel
      have hl : raw25765step3Labels = labelEmbedding1 ∘ raw25765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25765step3 raw25765step3Labels raw25765step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw25766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25766step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25766step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw25766step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25766step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw25766step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25766 raw25766Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw25766 raw25766Labels = mixedMoment B raw25766step0 raw25766step0Labels := by
      have hz : ∀ j, raw25766 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25766step0 = (fun i j => raw25766 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25766step0 raw25766; decide +kernel
      have hl : raw25766step0Labels = raw25766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766 raw25766Labels permutation520 hz
    mixedMoment B raw25766step0 raw25766step0Labels = mixedMoment B raw25766step1 raw25766step1Labels := by
      have hz : ∀ j, raw25766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25766step1 = (fun i j => raw25766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25766step1 raw25766step0; decide +kernel
      have hl : raw25766step1Labels = raw25766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766step0 raw25766step0Labels permutation80 hz
    mixedMoment B raw25766step1 raw25766step1Labels = mixedMoment B raw25766step2 raw25766step2Labels := by
      have hz : ∀ j, raw25766step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25766step2 = (fun i j => raw25766step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25766step2 raw25766step1; decide +kernel
      have hl : raw25766step2Labels = raw25766step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25766step1 raw25766step1Labels permutation14 hz
    mixedMoment B raw25766step2 raw25766step2Labels = mixedMoment B raw25766step3 raw25766step3Labels := by
      have ha : raw25766step3 = (fun i j => raw25766step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25766step3 raw25766step2; decide +kernel
      have hl : raw25766step3Labels = raw25766step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25766step2 raw25766step2Labels permutation3 permutation7
    mixedMoment B raw25766step3 raw25766step3Labels = mixedMoment B raw25766step4 raw25766step4Labels := by
      have ha : raw25766step4 = -raw25766step3 := by apply Matrix.ext; change ∀ i j, raw25766step4 i j = -(raw25766step3 i j); unfold raw25766step4 raw25766step3; decide +kernel
      have hl : raw25766step4Labels = raw25766step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25766step4 raw25766step4Labels = mixedMoment B raw25766step5 raw25766step5Labels := by
      have ha : raw25766step5 = raw25766step4 := by apply Matrix.ext; unfold raw25766step5 raw25766step4; decide +kernel
      have hl : raw25766step4Labels = labelEmbedding1 ∘ raw25766step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25766step4 raw25766step4Labels raw25766step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw25767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25767step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25767step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25767step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25767step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25767 raw25767Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw25767 raw25767Labels = mixedMoment B raw25767step0 raw25767step0Labels := by
      have hz : ∀ j, raw25767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25767step0 = (fun i j => raw25767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25767step0 raw25767; decide +kernel
      have hl : raw25767step0Labels = raw25767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25767 raw25767Labels permutation346 hz
    mixedMoment B raw25767step0 raw25767step0Labels = mixedMoment B raw25767step1 raw25767step1Labels := by
      have hz : ∀ j, raw25767step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25767step1 = (fun i j => raw25767step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25767step1 raw25767step0; decide +kernel
      have hl : raw25767step1Labels = raw25767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25767step0 raw25767step0Labels permutation56 hz
    mixedMoment B raw25767step1 raw25767step1Labels = mixedMoment B raw25767step2 raw25767step2Labels := by
      have ha : raw25767step2 = (fun i j => raw25767step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25767step2 raw25767step1; decide +kernel
      have hl : raw25767step2Labels = raw25767step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25767step1 raw25767step1Labels permutation11 permutation7
    mixedMoment B raw25767step2 raw25767step2Labels = mixedMoment B raw25767step3 raw25767step3Labels := by
      have ha : raw25767step3 = -raw25767step2 := by apply Matrix.ext; change ∀ i j, raw25767step3 i j = -(raw25767step2 i j); unfold raw25767step3 raw25767step2; decide +kernel
      have hl : raw25767step3Labels = raw25767step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25767step3 raw25767step3Labels = mixedMoment B raw25767step4 raw25767step4Labels := by
      have ha : raw25767step4 = raw25767step3 := by apply Matrix.ext; unfold raw25767step4 raw25767step3; decide +kernel
      have hl : raw25767step3Labels = labelEmbedding1 ∘ raw25767step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25767step3 raw25767step3Labels raw25767step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw25768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25768step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25768 raw25768Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw25768 raw25768Labels = mixedMoment B raw25768step0 raw25768step0Labels := by
      have hz : ∀ j, raw25768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25768step0 = (fun i j => raw25768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25768step0 raw25768; decide +kernel
      have hl : raw25768step0Labels = raw25768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25768 raw25768Labels permutation346 hz
    mixedMoment B raw25768step0 raw25768step0Labels = mixedMoment B raw25768step1 raw25768step1Labels := by
      have ha : raw25768step1 = (fun i j => raw25768step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25768step1 raw25768step0; decide +kernel
      have hl : raw25768step1Labels = raw25768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25768step0 raw25768step0Labels permutation35 permutation7
    mixedMoment B raw25768step1 raw25768step1Labels = mixedMoment B raw25768step2 raw25768step2Labels := by
      have ha : raw25768step2 = -raw25768step1 := by apply Matrix.ext; change ∀ i j, raw25768step2 i j = -(raw25768step1 i j); unfold raw25768step2 raw25768step1; decide +kernel
      have hl : raw25768step2Labels = raw25768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25768step2 raw25768step2Labels = mixedMoment B raw25768step3 raw25768step3Labels := by
      have ha : raw25768step3 = raw25768step2 := by apply Matrix.ext; unfold raw25768step3 raw25768step2; decide +kernel
      have hl : raw25768step2Labels = labelEmbedding1 ∘ raw25768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25768step2 raw25768step2Labels raw25768step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw25769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25769step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25769 raw25769Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw25769 raw25769Labels = mixedMoment B raw25769step0 raw25769step0Labels := by
      have ha : raw25769step0 = (fun i j => raw25769 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25769step0 raw25769; decide +kernel
      have hl : raw25769step0Labels = raw25769Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25769 raw25769Labels permutation179 permutation7
    mixedMoment B raw25769step0 raw25769step0Labels = mixedMoment B raw25769step1 raw25769step1Labels := by
      have ha : raw25769step1 = -raw25769step0 := by apply Matrix.ext; change ∀ i j, raw25769step1 i j = -(raw25769step0 i j); unfold raw25769step1 raw25769step0; decide +kernel
      have hl : raw25769step1Labels = raw25769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25769step1 raw25769step1Labels = mixedMoment B raw25769step2 raw25769step2Labels := by
      have ha : raw25769step2 = raw25769step1 := by apply Matrix.ext; unfold raw25769step2 raw25769step1; decide +kernel
      have hl : raw25769step1Labels = labelEmbedding1 ∘ raw25769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25769step1 raw25769step1Labels raw25769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

def raw25770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25770 raw25770Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw25770 raw25770Labels = mixedMoment B raw25770step0 raw25770step0Labels := by
      have hz : ∀ j, raw25770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25770step0 = (fun i j => raw25770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25770step0 raw25770; decide +kernel
      have hl : raw25770step0Labels = raw25770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25770 raw25770Labels permutation346 hz
    mixedMoment B raw25770step0 raw25770step0Labels = mixedMoment B raw25770step1 raw25770step1Labels := by
      have ha : raw25770step1 = (fun i j => raw25770step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25770step1 raw25770step0; decide +kernel
      have hl : raw25770step1Labels = raw25770step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25770step0 raw25770step0Labels permutation35 permutation7
    mixedMoment B raw25770step1 raw25770step1Labels = mixedMoment B raw25770step2 raw25770step2Labels := by
      have ha : raw25770step2 = -raw25770step1 := by apply Matrix.ext; change ∀ i j, raw25770step2 i j = -(raw25770step1 i j); unfold raw25770step2 raw25770step1; decide +kernel
      have hl : raw25770step2Labels = raw25770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25770step2 raw25770step2Labels = mixedMoment B raw25770step3 raw25770step3Labels := by
      have ha : raw25770step3 = raw25770step2 := by apply Matrix.ext; unfold raw25770step3 raw25770step2; decide +kernel
      have hl : raw25770step2Labels = labelEmbedding1 ∘ raw25770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25770step2 raw25770step2Labels raw25770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw25771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25771step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25771step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25771 raw25771Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25771 raw25771Labels = mixedMoment B raw25771step0 raw25771step0Labels := by
      have hz : ∀ j, raw25771 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25771step0 = (fun i j => raw25771 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25771step0 raw25771; decide +kernel
      have hl : raw25771step0Labels = raw25771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25771 raw25771Labels permutation520 hz
    mixedMoment B raw25771step0 raw25771step0Labels = mixedMoment B raw25771step1 raw25771step1Labels := by
      have hz : ∀ j, raw25771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25771step1 = (fun i j => raw25771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25771step1 raw25771step0; decide +kernel
      have hl : raw25771step1Labels = raw25771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25771step0 raw25771step0Labels permutation80 hz
    mixedMoment B raw25771step1 raw25771step1Labels = mixedMoment B raw25771step2 raw25771step2Labels := by
      have ha : raw25771step2 = (fun i j => raw25771step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25771step2 raw25771step1; decide +kernel
      have hl : raw25771step2Labels = raw25771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25771step1 raw25771step1Labels permutation9 permutation7
    mixedMoment B raw25771step2 raw25771step2Labels = mixedMoment B raw25771step3 raw25771step3Labels := by
      have ha : raw25771step3 = -raw25771step2 := by apply Matrix.ext; change ∀ i j, raw25771step3 i j = -(raw25771step2 i j); unfold raw25771step3 raw25771step2; decide +kernel
      have hl : raw25771step3Labels = raw25771step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25771step3 raw25771step3Labels = mixedMoment B raw25771step4 raw25771step4Labels := by
      have ha : raw25771step4 = raw25771step3 := by apply Matrix.ext; unfold raw25771step4 raw25771step3; decide +kernel
      have hl : raw25771step3Labels = labelEmbedding1 ∘ raw25771step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25771step3 raw25771step3Labels raw25771step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw25772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25772step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25772step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25772step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25772 raw25772Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25772 raw25772Labels = mixedMoment B raw25772step0 raw25772step0Labels := by
      have hz : ∀ j, raw25772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25772step0 = (fun i j => raw25772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25772step0 raw25772; decide +kernel
      have hl : raw25772step0Labels = raw25772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25772 raw25772Labels permutation346 hz
    mixedMoment B raw25772step0 raw25772step0Labels = mixedMoment B raw25772step1 raw25772step1Labels := by
      have ha : raw25772step1 = (fun i j => raw25772step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25772step1 raw25772step0; decide +kernel
      have hl : raw25772step1Labels = raw25772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25772step0 raw25772step0Labels permutation35 permutation7
    mixedMoment B raw25772step1 raw25772step1Labels = mixedMoment B raw25772step2 raw25772step2Labels := by
      have ha : raw25772step2 = -raw25772step1 := by apply Matrix.ext; change ∀ i j, raw25772step2 i j = -(raw25772step1 i j); unfold raw25772step2 raw25772step1; decide +kernel
      have hl : raw25772step2Labels = raw25772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25772step2 raw25772step2Labels = mixedMoment B raw25772step3 raw25772step3Labels := by
      have ha : raw25772step3 = raw25772step2 := by apply Matrix.ext; unfold raw25772step3 raw25772step2; decide +kernel
      have hl : raw25772step2Labels = labelEmbedding1 ∘ raw25772step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25772step2 raw25772step2Labels raw25772step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw25773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25773step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25773 raw25773Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw25773 raw25773Labels = mixedMoment B raw25773step0 raw25773step0Labels := by
      have hz : ∀ j, raw25773 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25773step0 = (fun i j => raw25773 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25773step0 raw25773; decide +kernel
      have hl : raw25773step0Labels = raw25773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25773 raw25773Labels permutation265 hz
    mixedMoment B raw25773step0 raw25773step0Labels = mixedMoment B raw25773step1 raw25773step1Labels := by
      have ha : raw25773step1 = (fun i j => raw25773step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25773step1 raw25773step0; decide +kernel
      have hl : raw25773step1Labels = raw25773step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25773step0 raw25773step0Labels permutation35 permutation7
    mixedMoment B raw25773step1 raw25773step1Labels = mixedMoment B raw25773step2 raw25773step2Labels := by
      have ha : raw25773step2 = -raw25773step1 := by apply Matrix.ext; change ∀ i j, raw25773step2 i j = -(raw25773step1 i j); unfold raw25773step2 raw25773step1; decide +kernel
      have hl : raw25773step2Labels = raw25773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25773step2 raw25773step2Labels = mixedMoment B raw25773step3 raw25773step3Labels := by
      have ha : raw25773step3 = raw25773step2 := by apply Matrix.ext; unfold raw25773step3 raw25773step2; decide +kernel
      have hl : raw25773step2Labels = labelEmbedding1 ∘ raw25773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25773step2 raw25773step2Labels raw25773step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw25774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25774 raw25774Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw25774 raw25774Labels = mixedMoment B raw25774step0 raw25774step0Labels := by
      have ha : raw25774step0 = (fun i j => raw25774 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25774step0 raw25774; decide +kernel
      have hl : raw25774step0Labels = raw25774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25774 raw25774Labels permutation155 permutation7
    mixedMoment B raw25774step0 raw25774step0Labels = mixedMoment B raw25774step1 raw25774step1Labels := by
      have ha : raw25774step1 = -raw25774step0 := by apply Matrix.ext; change ∀ i j, raw25774step1 i j = -(raw25774step0 i j); unfold raw25774step1 raw25774step0; decide +kernel
      have hl : raw25774step1Labels = raw25774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25774step1 raw25774step1Labels = mixedMoment B raw25774step2 raw25774step2Labels := by
      have ha : raw25774step2 = raw25774step1 := by apply Matrix.ext; unfold raw25774step2 raw25774step1; decide +kernel
      have hl : raw25774step1Labels = labelEmbedding1 ∘ raw25774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25774step1 raw25774step1Labels raw25774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

def raw25775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25775step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25775step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25775 raw25775Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw25775 raw25775Labels = mixedMoment B raw25775step0 raw25775step0Labels := by
      have hz : ∀ j, raw25775 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25775step0 = (fun i j => raw25775 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25775step0 raw25775; decide +kernel
      have hl : raw25775step0Labels = raw25775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25775 raw25775Labels permutation265 hz
    mixedMoment B raw25775step0 raw25775step0Labels = mixedMoment B raw25775step1 raw25775step1Labels := by
      have ha : raw25775step1 = (fun i j => raw25775step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25775step1 raw25775step0; decide +kernel
      have hl : raw25775step1Labels = raw25775step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25775step0 raw25775step0Labels permutation35 permutation7
    mixedMoment B raw25775step1 raw25775step1Labels = mixedMoment B raw25775step2 raw25775step2Labels := by
      have ha : raw25775step2 = -raw25775step1 := by apply Matrix.ext; change ∀ i j, raw25775step2 i j = -(raw25775step1 i j); unfold raw25775step2 raw25775step1; decide +kernel
      have hl : raw25775step2Labels = raw25775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25775step2 raw25775step2Labels = mixedMoment B raw25775step3 raw25775step3Labels := by
      have ha : raw25775step3 = raw25775step2 := by apply Matrix.ext; unfold raw25775step3 raw25775step2; decide +kernel
      have hl : raw25775step2Labels = labelEmbedding1 ∘ raw25775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25775step2 raw25775step2Labels raw25775step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw25776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25776step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw25776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25776step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25776 raw25776Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw25776 raw25776Labels = mixedMoment B raw25776step0 raw25776step0Labels := by
      have hz : ∀ j, raw25776 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25776step0 = (fun i j => raw25776 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25776step0 raw25776; decide +kernel
      have hl : raw25776step0Labels = raw25776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25776 raw25776Labels permutation520 hz
    mixedMoment B raw25776step0 raw25776step0Labels = mixedMoment B raw25776step1 raw25776step1Labels := by
      have hz : ∀ j, raw25776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25776step1 = (fun i j => raw25776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25776step1 raw25776step0; decide +kernel
      have hl : raw25776step1Labels = raw25776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25776step0 raw25776step0Labels permutation56 hz
    mixedMoment B raw25776step1 raw25776step1Labels = mixedMoment B raw25776step2 raw25776step2Labels := by
      have ha : raw25776step2 = (fun i j => raw25776step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25776step2 raw25776step1; decide +kernel
      have hl : raw25776step2Labels = raw25776step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25776step1 raw25776step1Labels permutation9 permutation7
    mixedMoment B raw25776step2 raw25776step2Labels = mixedMoment B raw25776step3 raw25776step3Labels := by
      have ha : raw25776step3 = -raw25776step2 := by apply Matrix.ext; change ∀ i j, raw25776step3 i j = -(raw25776step2 i j); unfold raw25776step3 raw25776step2; decide +kernel
      have hl : raw25776step3Labels = raw25776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25776step3 raw25776step3Labels = mixedMoment B raw25776step4 raw25776step4Labels := by
      have ha : raw25776step4 = raw25776step3 := by apply Matrix.ext; unfold raw25776step4 raw25776step3; decide +kernel
      have hl : raw25776step3Labels = labelEmbedding1 ∘ raw25776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25776step3 raw25776step3Labels raw25776step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw25777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25777step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25777step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25777 raw25777Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25777 raw25777Labels = mixedMoment B raw25777step0 raw25777step0Labels := by
      have hz : ∀ j, raw25777 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25777step0 = (fun i j => raw25777 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25777step0 raw25777; decide +kernel
      have hl : raw25777step0Labels = raw25777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25777 raw25777Labels permutation265 hz
    mixedMoment B raw25777step0 raw25777step0Labels = mixedMoment B raw25777step1 raw25777step1Labels := by
      have ha : raw25777step1 = (fun i j => raw25777step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25777step1 raw25777step0; decide +kernel
      have hl : raw25777step1Labels = raw25777step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25777step0 raw25777step0Labels permutation35 permutation7
    mixedMoment B raw25777step1 raw25777step1Labels = mixedMoment B raw25777step2 raw25777step2Labels := by
      have ha : raw25777step2 = -raw25777step1 := by apply Matrix.ext; change ∀ i j, raw25777step2 i j = -(raw25777step1 i j); unfold raw25777step2 raw25777step1; decide +kernel
      have hl : raw25777step2Labels = raw25777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25777step2 raw25777step2Labels = mixedMoment B raw25777step3 raw25777step3Labels := by
      have ha : raw25777step3 = raw25777step2 := by apply Matrix.ext; unfold raw25777step3 raw25777step2; decide +kernel
      have hl : raw25777step2Labels = labelEmbedding1 ∘ raw25777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25777step2 raw25777step2Labels raw25777step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw25778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25778step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25778step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25778 raw25778Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw25778 raw25778Labels = mixedMoment B raw25778step0 raw25778step0Labels := by
      have hz : ∀ j, raw25778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25778step0 = (fun i j => raw25778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25778step0 raw25778; decide +kernel
      have hl : raw25778step0Labels = raw25778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25778 raw25778Labels permutation346 hz
    mixedMoment B raw25778step0 raw25778step0Labels = mixedMoment B raw25778step1 raw25778step1Labels := by
      have hz : ∀ j, raw25778step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25778step1 = (fun i j => raw25778step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25778step1 raw25778step0; decide +kernel
      have hl : raw25778step1Labels = raw25778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25778step0 raw25778step0Labels permutation56 hz
    mixedMoment B raw25778step1 raw25778step1Labels = mixedMoment B raw25778step2 raw25778step2Labels := by
      have ha : raw25778step2 = (fun i j => raw25778step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25778step2 raw25778step1; decide +kernel
      have hl : raw25778step2Labels = raw25778step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25778step1 raw25778step1Labels permutation11 permutation7
    mixedMoment B raw25778step2 raw25778step2Labels = mixedMoment B raw25778step3 raw25778step3Labels := by
      have ha : raw25778step3 = -raw25778step2 := by apply Matrix.ext; change ∀ i j, raw25778step3 i j = -(raw25778step2 i j); unfold raw25778step3 raw25778step2; decide +kernel
      have hl : raw25778step3Labels = raw25778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25778step3 raw25778step3Labels = mixedMoment B raw25778step4 raw25778step4Labels := by
      have ha : raw25778step4 = raw25778step3 := by apply Matrix.ext; unfold raw25778step4 raw25778step3; decide +kernel
      have hl : raw25778step3Labels = labelEmbedding1 ∘ raw25778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25778step3 raw25778step3Labels raw25778step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw25779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25779 raw25779Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw25779 raw25779Labels = mixedMoment B raw25779step0 raw25779step0Labels := by
      have hz : ∀ j, raw25779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25779step0 = (fun i j => raw25779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25779step0 raw25779; decide +kernel
      have hl : raw25779step0Labels = raw25779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25779 raw25779Labels permutation346 hz
    mixedMoment B raw25779step0 raw25779step0Labels = mixedMoment B raw25779step1 raw25779step1Labels := by
      have ha : raw25779step1 = (fun i j => raw25779step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25779step1 raw25779step0; decide +kernel
      have hl : raw25779step1Labels = raw25779step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25779step0 raw25779step0Labels permutation35 permutation7
    mixedMoment B raw25779step1 raw25779step1Labels = mixedMoment B raw25779step2 raw25779step2Labels := by
      have ha : raw25779step2 = -raw25779step1 := by apply Matrix.ext; change ∀ i j, raw25779step2 i j = -(raw25779step1 i j); unfold raw25779step2 raw25779step1; decide +kernel
      have hl : raw25779step2Labels = raw25779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25779step2 raw25779step2Labels = mixedMoment B raw25779step3 raw25779step3Labels := by
      have ha : raw25779step3 = raw25779step2 := by apply Matrix.ext; unfold raw25779step3 raw25779step2; decide +kernel
      have hl : raw25779step2Labels = labelEmbedding1 ∘ raw25779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25779step2 raw25779step2Labels raw25779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw25780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw25780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25780step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw25780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25780 raw25780Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw25780 raw25780Labels = mixedMoment B raw25780step0 raw25780step0Labels := by
      have hz : ∀ j, raw25780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25780step0 = (fun i j => raw25780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25780step0 raw25780; decide +kernel
      have hl : raw25780step0Labels = raw25780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25780 raw25780Labels permutation265 hz
    mixedMoment B raw25780step0 raw25780step0Labels = mixedMoment B raw25780step1 raw25780step1Labels := by
      have ha : raw25780step1 = (fun i j => raw25780step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25780step1 raw25780step0; decide +kernel
      have hl : raw25780step1Labels = raw25780step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25780step0 raw25780step0Labels permutation35 permutation7
    mixedMoment B raw25780step1 raw25780step1Labels = mixedMoment B raw25780step2 raw25780step2Labels := by
      have ha : raw25780step2 = -raw25780step1 := by apply Matrix.ext; change ∀ i j, raw25780step2 i j = -(raw25780step1 i j); unfold raw25780step2 raw25780step1; decide +kernel
      have hl : raw25780step2Labels = raw25780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25780step2 raw25780step2Labels = mixedMoment B raw25780step3 raw25780step3Labels := by
      have ha : raw25780step3 = raw25780step2 := by apply Matrix.ext; unfold raw25780step3 raw25780step2; decide +kernel
      have hl : raw25780step2Labels = labelEmbedding1 ∘ raw25780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25780step2 raw25780step2Labels raw25780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw25781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw25781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw25781step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw25781step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw25781step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25781step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw25781step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25781 raw25781Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw25781 raw25781Labels = mixedMoment B raw25781step0 raw25781step0Labels := by
      have hz : ∀ j, raw25781 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25781step0 = (fun i j => raw25781 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25781step0 raw25781; decide +kernel
      have hl : raw25781step0Labels = raw25781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781 raw25781Labels permutation520 hz
    mixedMoment B raw25781step0 raw25781step0Labels = mixedMoment B raw25781step1 raw25781step1Labels := by
      have hz : ∀ j, raw25781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25781step1 = (fun i j => raw25781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25781step1 raw25781step0; decide +kernel
      have hl : raw25781step1Labels = raw25781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781step0 raw25781step0Labels permutation80 hz
    mixedMoment B raw25781step1 raw25781step1Labels = mixedMoment B raw25781step2 raw25781step2Labels := by
      have hz : ∀ j, raw25781step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25781step2 = (fun i j => raw25781step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25781step2 raw25781step1; decide +kernel
      have hl : raw25781step2Labels = raw25781step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25781step1 raw25781step1Labels permutation14 hz
    mixedMoment B raw25781step2 raw25781step2Labels = mixedMoment B raw25781step3 raw25781step3Labels := by
      have ha : raw25781step3 = (fun i j => raw25781step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25781step3 raw25781step2; decide +kernel
      have hl : raw25781step3Labels = raw25781step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25781step2 raw25781step2Labels permutation3 permutation7
    mixedMoment B raw25781step3 raw25781step3Labels = mixedMoment B raw25781step4 raw25781step4Labels := by
      have ha : raw25781step4 = -raw25781step3 := by apply Matrix.ext; change ∀ i j, raw25781step4 i j = -(raw25781step3 i j); unfold raw25781step4 raw25781step3; decide +kernel
      have hl : raw25781step4Labels = raw25781step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25781step4 raw25781step4Labels = mixedMoment B raw25781step5 raw25781step5Labels := by
      have ha : raw25781step5 = raw25781step4 := by apply Matrix.ext; unfold raw25781step5 raw25781step4; decide +kernel
      have hl : raw25781step4Labels = labelEmbedding1 ∘ raw25781step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25781step4 raw25781step4Labels raw25781step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw25782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw25782step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25782step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25782step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25782 raw25782Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25782 raw25782Labels = mixedMoment B raw25782step0 raw25782step0Labels := by
      have hz : ∀ j, raw25782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25782step0 = (fun i j => raw25782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25782step0 raw25782; decide +kernel
      have hl : raw25782step0Labels = raw25782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25782 raw25782Labels permutation346 hz
    mixedMoment B raw25782step0 raw25782step0Labels = mixedMoment B raw25782step1 raw25782step1Labels := by
      have hz : ∀ j, raw25782step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25782step1 = (fun i j => raw25782step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25782step1 raw25782step0; decide +kernel
      have hl : raw25782step1Labels = raw25782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25782step0 raw25782step0Labels permutation56 hz
    mixedMoment B raw25782step1 raw25782step1Labels = mixedMoment B raw25782step2 raw25782step2Labels := by
      have ha : raw25782step2 = (fun i j => raw25782step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25782step2 raw25782step1; decide +kernel
      have hl : raw25782step2Labels = raw25782step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25782step1 raw25782step1Labels permutation11 permutation7
    mixedMoment B raw25782step2 raw25782step2Labels = mixedMoment B raw25782step3 raw25782step3Labels := by
      have ha : raw25782step3 = -raw25782step2 := by apply Matrix.ext; change ∀ i j, raw25782step3 i j = -(raw25782step2 i j); unfold raw25782step3 raw25782step2; decide +kernel
      have hl : raw25782step3Labels = raw25782step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25782step3 raw25782step3Labels = mixedMoment B raw25782step4 raw25782step4Labels := by
      have ha : raw25782step4 = raw25782step3 := by apply Matrix.ext; unfold raw25782step4 raw25782step3; decide +kernel
      have hl : raw25782step3Labels = labelEmbedding1 ∘ raw25782step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25782step3 raw25782step3Labels raw25782step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw25783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25783step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25783step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25783step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25783step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25783 raw25783Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw25783 raw25783Labels = mixedMoment B raw25783step0 raw25783step0Labels := by
      have hz : ∀ j, raw25783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25783step0 = (fun i j => raw25783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25783step0 raw25783; decide +kernel
      have hl : raw25783step0Labels = raw25783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25783 raw25783Labels permutation346 hz
    mixedMoment B raw25783step0 raw25783step0Labels = mixedMoment B raw25783step1 raw25783step1Labels := by
      have hz : ∀ j, raw25783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25783step1 = (fun i j => raw25783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25783step1 raw25783step0; decide +kernel
      have hl : raw25783step1Labels = raw25783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25783step0 raw25783step0Labels permutation56 hz
    mixedMoment B raw25783step1 raw25783step1Labels = mixedMoment B raw25783step2 raw25783step2Labels := by
      have ha : raw25783step2 = (fun i j => raw25783step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25783step2 raw25783step1; decide +kernel
      have hl : raw25783step2Labels = raw25783step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25783step1 raw25783step1Labels permutation11 permutation7
    mixedMoment B raw25783step2 raw25783step2Labels = mixedMoment B raw25783step3 raw25783step3Labels := by
      have ha : raw25783step3 = -raw25783step2 := by apply Matrix.ext; change ∀ i j, raw25783step3 i j = -(raw25783step2 i j); unfold raw25783step3 raw25783step2; decide +kernel
      have hl : raw25783step3Labels = raw25783step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25783step3 raw25783step3Labels = mixedMoment B raw25783step4 raw25783step4Labels := by
      have ha : raw25783step4 = raw25783step3 := by apply Matrix.ext; unfold raw25783step4 raw25783step3; decide +kernel
      have hl : raw25783step3Labels = labelEmbedding1 ∘ raw25783step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25783step3 raw25783step3Labels raw25783step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw25784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25784 raw25784Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25784 raw25784Labels = mixedMoment B raw25784step0 raw25784step0Labels := by
      have hz : ∀ j, raw25784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25784step0 = (fun i j => raw25784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25784step0 raw25784; decide +kernel
      have hl : raw25784step0Labels = raw25784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25784 raw25784Labels permutation346 hz
    mixedMoment B raw25784step0 raw25784step0Labels = mixedMoment B raw25784step1 raw25784step1Labels := by
      have ha : raw25784step1 = (fun i j => raw25784step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25784step1 raw25784step0; decide +kernel
      have hl : raw25784step1Labels = raw25784step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25784step0 raw25784step0Labels permutation35 permutation7
    mixedMoment B raw25784step1 raw25784step1Labels = mixedMoment B raw25784step2 raw25784step2Labels := by
      have ha : raw25784step2 = -raw25784step1 := by apply Matrix.ext; change ∀ i j, raw25784step2 i j = -(raw25784step1 i j); unfold raw25784step2 raw25784step1; decide +kernel
      have hl : raw25784step2Labels = raw25784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25784step2 raw25784step2Labels = mixedMoment B raw25784step3 raw25784step3Labels := by
      have ha : raw25784step3 = raw25784step2 := by apply Matrix.ext; unfold raw25784step3 raw25784step2; decide +kernel
      have hl : raw25784step2Labels = labelEmbedding1 ∘ raw25784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25784step2 raw25784step2Labels raw25784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw25785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25785step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw25785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25785step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw25785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25785 raw25785Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw25785 raw25785Labels = mixedMoment B raw25785step0 raw25785step0Labels := by
      have hz : ∀ j, raw25785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25785step0 = (fun i j => raw25785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25785step0 raw25785; decide +kernel
      have hl : raw25785step0Labels = raw25785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25785 raw25785Labels permutation265 hz
    mixedMoment B raw25785step0 raw25785step0Labels = mixedMoment B raw25785step1 raw25785step1Labels := by
      have ha : raw25785step1 = (fun i j => raw25785step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25785step1 raw25785step0; decide +kernel
      have hl : raw25785step1Labels = raw25785step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25785step0 raw25785step0Labels permutation35 permutation7
    mixedMoment B raw25785step1 raw25785step1Labels = mixedMoment B raw25785step2 raw25785step2Labels := by
      have ha : raw25785step2 = -raw25785step1 := by apply Matrix.ext; change ∀ i j, raw25785step2 i j = -(raw25785step1 i j); unfold raw25785step2 raw25785step1; decide +kernel
      have hl : raw25785step2Labels = raw25785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25785step2 raw25785step2Labels = mixedMoment B raw25785step3 raw25785step3Labels := by
      have ha : raw25785step3 = raw25785step2 := by apply Matrix.ext; unfold raw25785step3 raw25785step2; decide +kernel
      have hl : raw25785step2Labels = labelEmbedding1 ∘ raw25785step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25785step2 raw25785step2Labels raw25785step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw25786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw25786step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw25786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25786step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw25786step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25786 raw25786Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw25786 raw25786Labels = mixedMoment B raw25786step0 raw25786step0Labels := by
      have hz : ∀ j, raw25786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25786step0 = (fun i j => raw25786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25786step0 raw25786; decide +kernel
      have hl : raw25786step0Labels = raw25786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25786 raw25786Labels permutation346 hz
    mixedMoment B raw25786step0 raw25786step0Labels = mixedMoment B raw25786step1 raw25786step1Labels := by
      have hz : ∀ j, raw25786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25786step1 = (fun i j => raw25786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25786step1 raw25786step0; decide +kernel
      have hl : raw25786step1Labels = raw25786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25786step0 raw25786step0Labels permutation56 hz
    mixedMoment B raw25786step1 raw25786step1Labels = mixedMoment B raw25786step2 raw25786step2Labels := by
      have ha : raw25786step2 = (fun i j => raw25786step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25786step2 raw25786step1; decide +kernel
      have hl : raw25786step2Labels = raw25786step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25786step1 raw25786step1Labels permutation11 permutation7
    mixedMoment B raw25786step2 raw25786step2Labels = mixedMoment B raw25786step3 raw25786step3Labels := by
      have ha : raw25786step3 = -raw25786step2 := by apply Matrix.ext; change ∀ i j, raw25786step3 i j = -(raw25786step2 i j); unfold raw25786step3 raw25786step2; decide +kernel
      have hl : raw25786step3Labels = raw25786step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25786step3 raw25786step3Labels = mixedMoment B raw25786step4 raw25786step4Labels := by
      have ha : raw25786step4 = raw25786step3 := by apply Matrix.ext; unfold raw25786step4 raw25786step3; decide +kernel
      have hl : raw25786step3Labels = labelEmbedding1 ∘ raw25786step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25786step3 raw25786step3Labels raw25786step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw25787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw25787step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw25787step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25787step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw25787step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25787 raw25787Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw25787 raw25787Labels = mixedMoment B raw25787step0 raw25787step0Labels := by
      have hz : ∀ j, raw25787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25787step0 = (fun i j => raw25787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25787step0 raw25787; decide +kernel
      have hl : raw25787step0Labels = raw25787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25787 raw25787Labels permutation346 hz
    mixedMoment B raw25787step0 raw25787step0Labels = mixedMoment B raw25787step1 raw25787step1Labels := by
      have hz : ∀ j, raw25787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25787step1 = (fun i j => raw25787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25787step1 raw25787step0; decide +kernel
      have hl : raw25787step1Labels = raw25787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25787step0 raw25787step0Labels permutation56 hz
    mixedMoment B raw25787step1 raw25787step1Labels = mixedMoment B raw25787step2 raw25787step2Labels := by
      have ha : raw25787step2 = (fun i j => raw25787step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25787step2 raw25787step1; decide +kernel
      have hl : raw25787step2Labels = raw25787step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25787step1 raw25787step1Labels permutation11 permutation7
    mixedMoment B raw25787step2 raw25787step2Labels = mixedMoment B raw25787step3 raw25787step3Labels := by
      have ha : raw25787step3 = -raw25787step2 := by apply Matrix.ext; change ∀ i j, raw25787step3 i j = -(raw25787step2 i j); unfold raw25787step3 raw25787step2; decide +kernel
      have hl : raw25787step3Labels = raw25787step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25787step3 raw25787step3Labels = mixedMoment B raw25787step4 raw25787step4Labels := by
      have ha : raw25787step4 = raw25787step3 := by apply Matrix.ext; unfold raw25787step4 raw25787step3; decide +kernel
      have hl : raw25787step3Labels = labelEmbedding1 ∘ raw25787step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25787step3 raw25787step3Labels raw25787step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw25788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25788step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25788step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25788step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25788 raw25788Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw25788 raw25788Labels = mixedMoment B raw25788step0 raw25788step0Labels := by
      have hz : ∀ j, raw25788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25788step0 = (fun i j => raw25788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25788step0 raw25788; decide +kernel
      have hl : raw25788step0Labels = raw25788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25788 raw25788Labels permutation346 hz
    mixedMoment B raw25788step0 raw25788step0Labels = mixedMoment B raw25788step1 raw25788step1Labels := by
      have hz : ∀ j, raw25788step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25788step1 = (fun i j => raw25788step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25788step1 raw25788step0; decide +kernel
      have hl : raw25788step1Labels = raw25788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25788step0 raw25788step0Labels permutation56 hz
    mixedMoment B raw25788step1 raw25788step1Labels = mixedMoment B raw25788step2 raw25788step2Labels := by
      have ha : raw25788step2 = (fun i j => raw25788step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25788step2 raw25788step1; decide +kernel
      have hl : raw25788step2Labels = raw25788step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25788step1 raw25788step1Labels permutation11 permutation7
    mixedMoment B raw25788step2 raw25788step2Labels = mixedMoment B raw25788step3 raw25788step3Labels := by
      have ha : raw25788step3 = -raw25788step2 := by apply Matrix.ext; change ∀ i j, raw25788step3 i j = -(raw25788step2 i j); unfold raw25788step3 raw25788step2; decide +kernel
      have hl : raw25788step3Labels = raw25788step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25788step3 raw25788step3Labels = mixedMoment B raw25788step4 raw25788step4Labels := by
      have ha : raw25788step4 = raw25788step3 := by apply Matrix.ext; unfold raw25788step4 raw25788step3; decide +kernel
      have hl : raw25788step3Labels = labelEmbedding1 ∘ raw25788step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25788step3 raw25788step3Labels raw25788step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw25789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25789step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25789step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25789 raw25789Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw25789 raw25789Labels = mixedMoment B raw25789step0 raw25789step0Labels := by
      have hz : ∀ j, raw25789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25789step0 = (fun i j => raw25789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25789step0 raw25789; decide +kernel
      have hl : raw25789step0Labels = raw25789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25789 raw25789Labels permutation346 hz
    mixedMoment B raw25789step0 raw25789step0Labels = mixedMoment B raw25789step1 raw25789step1Labels := by
      have ha : raw25789step1 = (fun i j => raw25789step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25789step1 raw25789step0; decide +kernel
      have hl : raw25789step1Labels = raw25789step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25789step0 raw25789step0Labels permutation35 permutation7
    mixedMoment B raw25789step1 raw25789step1Labels = mixedMoment B raw25789step2 raw25789step2Labels := by
      have ha : raw25789step2 = -raw25789step1 := by apply Matrix.ext; change ∀ i j, raw25789step2 i j = -(raw25789step1 i j); unfold raw25789step2 raw25789step1; decide +kernel
      have hl : raw25789step2Labels = raw25789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25789step2 raw25789step2Labels = mixedMoment B raw25789step3 raw25789step3Labels := by
      have ha : raw25789step3 = raw25789step2 := by apply Matrix.ext; unfold raw25789step3 raw25789step2; decide +kernel
      have hl : raw25789step2Labels = labelEmbedding1 ∘ raw25789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25789step2 raw25789step2Labels raw25789step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw25790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw25790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw25790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25790 raw25790Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw25790 raw25790Labels = mixedMoment B raw25790step0 raw25790step0Labels := by
      have hz : ∀ j, raw25790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25790step0 = (fun i j => raw25790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25790step0 raw25790; decide +kernel
      have hl : raw25790step0Labels = raw25790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25790 raw25790Labels permutation265 hz
    mixedMoment B raw25790step0 raw25790step0Labels = mixedMoment B raw25790step1 raw25790step1Labels := by
      have ha : raw25790step1 = (fun i j => raw25790step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25790step1 raw25790step0; decide +kernel
      have hl : raw25790step1Labels = raw25790step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25790step0 raw25790step0Labels permutation35 permutation7
    mixedMoment B raw25790step1 raw25790step1Labels = mixedMoment B raw25790step2 raw25790step2Labels := by
      have ha : raw25790step2 = -raw25790step1 := by apply Matrix.ext; change ∀ i j, raw25790step2 i j = -(raw25790step1 i j); unfold raw25790step2 raw25790step1; decide +kernel
      have hl : raw25790step2Labels = raw25790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25790step2 raw25790step2Labels = mixedMoment B raw25790step3 raw25790step3Labels := by
      have ha : raw25790step3 = raw25790step2 := by apply Matrix.ext; unfold raw25790step3 raw25790step2; decide +kernel
      have hl : raw25790step2Labels = labelEmbedding1 ∘ raw25790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25790step2 raw25790step2Labels raw25790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw25791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw25791step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw25791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25791step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw25791step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25791 raw25791Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw25791 raw25791Labels = mixedMoment B raw25791step0 raw25791step0Labels := by
      have hz : ∀ j, raw25791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25791step0 = (fun i j => raw25791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25791step0 raw25791; decide +kernel
      have hl : raw25791step0Labels = raw25791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25791 raw25791Labels permutation346 hz
    mixedMoment B raw25791step0 raw25791step0Labels = mixedMoment B raw25791step1 raw25791step1Labels := by
      have hz : ∀ j, raw25791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25791step1 = (fun i j => raw25791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25791step1 raw25791step0; decide +kernel
      have hl : raw25791step1Labels = raw25791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25791step0 raw25791step0Labels permutation56 hz
    mixedMoment B raw25791step1 raw25791step1Labels = mixedMoment B raw25791step2 raw25791step2Labels := by
      have ha : raw25791step2 = (fun i j => raw25791step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25791step2 raw25791step1; decide +kernel
      have hl : raw25791step2Labels = raw25791step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25791step1 raw25791step1Labels permutation11 permutation7
    mixedMoment B raw25791step2 raw25791step2Labels = mixedMoment B raw25791step3 raw25791step3Labels := by
      have ha : raw25791step3 = -raw25791step2 := by apply Matrix.ext; change ∀ i j, raw25791step3 i j = -(raw25791step2 i j); unfold raw25791step3 raw25791step2; decide +kernel
      have hl : raw25791step3Labels = raw25791step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25791step3 raw25791step3Labels = mixedMoment B raw25791step4 raw25791step4Labels := by
      have ha : raw25791step4 = raw25791step3 := by apply Matrix.ext; unfold raw25791step4 raw25791step3; decide +kernel
      have hl : raw25791step3Labels = labelEmbedding1 ∘ raw25791step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25791step3 raw25791step3Labels raw25791step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw25792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw25792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw25792step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw25792step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25792step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw25792step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25792step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw25792step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25792 raw25792Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw25792 raw25792Labels = mixedMoment B raw25792step0 raw25792step0Labels := by
      have hz : ∀ j, raw25792 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25792step0 = (fun i j => raw25792 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25792step0 raw25792; decide +kernel
      have hl : raw25792step0Labels = raw25792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792 raw25792Labels permutation520 hz
    mixedMoment B raw25792step0 raw25792step0Labels = mixedMoment B raw25792step1 raw25792step1Labels := by
      have hz : ∀ j, raw25792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25792step1 = (fun i j => raw25792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25792step1 raw25792step0; decide +kernel
      have hl : raw25792step1Labels = raw25792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792step0 raw25792step0Labels permutation80 hz
    mixedMoment B raw25792step1 raw25792step1Labels = mixedMoment B raw25792step2 raw25792step2Labels := by
      have hz : ∀ j, raw25792step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25792step2 = (fun i j => raw25792step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25792step2 raw25792step1; decide +kernel
      have hl : raw25792step2Labels = raw25792step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25792step1 raw25792step1Labels permutation14 hz
    mixedMoment B raw25792step2 raw25792step2Labels = mixedMoment B raw25792step3 raw25792step3Labels := by
      have ha : raw25792step3 = (fun i j => raw25792step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25792step3 raw25792step2; decide +kernel
      have hl : raw25792step3Labels = raw25792step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25792step2 raw25792step2Labels permutation3 permutation7
    mixedMoment B raw25792step3 raw25792step3Labels = mixedMoment B raw25792step4 raw25792step4Labels := by
      have ha : raw25792step4 = -raw25792step3 := by apply Matrix.ext; change ∀ i j, raw25792step4 i j = -(raw25792step3 i j); unfold raw25792step4 raw25792step3; decide +kernel
      have hl : raw25792step4Labels = raw25792step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25792step4 raw25792step4Labels = mixedMoment B raw25792step5 raw25792step5Labels := by
      have ha : raw25792step5 = raw25792step4 := by apply Matrix.ext; unfold raw25792step5 raw25792step4; decide +kernel
      have hl : raw25792step4Labels = labelEmbedding1 ∘ raw25792step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25792step4 raw25792step4Labels raw25792step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw25793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25793 raw25793Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw25793 raw25793Labels = mixedMoment B raw25793step0 raw25793step0Labels := by
      have hz : ∀ j, raw25793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25793step0 = (fun i j => raw25793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25793step0 raw25793; decide +kernel
      have hl : raw25793step0Labels = raw25793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25793 raw25793Labels permutation346 hz
    mixedMoment B raw25793step0 raw25793step0Labels = mixedMoment B raw25793step1 raw25793step1Labels := by
      have ha : raw25793step1 = (fun i j => raw25793step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25793step1 raw25793step0; decide +kernel
      have hl : raw25793step1Labels = raw25793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25793step0 raw25793step0Labels permutation44 permutation3
    mixedMoment B raw25793step1 raw25793step1Labels = mixedMoment B raw25793step2 raw25793step2Labels := by
      have ha : raw25793step2 = raw25793step1 := by apply Matrix.ext; unfold raw25793step2 raw25793step1; decide +kernel
      have hl : raw25793step1Labels = labelEmbedding6 ∘ raw25793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25793step1 raw25793step1Labels raw25793step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw25794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25794 raw25794Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw25794 raw25794Labels = mixedMoment B raw25794step0 raw25794step0Labels := by
      have ha : raw25794step0 = (fun i j => raw25794 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25794step0 raw25794; decide +kernel
      have hl : raw25794step0Labels = raw25794Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25794 raw25794Labels permutation188 permutation3
    mixedMoment B raw25794step0 raw25794step0Labels = mixedMoment B raw25794step1 raw25794step1Labels := by
      have ha : raw25794step1 = raw25794step0 := by apply Matrix.ext; unfold raw25794step1 raw25794step0; decide +kernel
      have hl : raw25794step0Labels = labelEmbedding6 ∘ raw25794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25794step0 raw25794step0Labels raw25794step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw25795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25795 raw25795Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw25795 raw25795Labels = mixedMoment B raw25795step0 raw25795step0Labels := by
      have hz : ∀ j, raw25795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25795step0 = (fun i j => raw25795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25795step0 raw25795; decide +kernel
      have hl : raw25795step0Labels = raw25795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25795 raw25795Labels permutation346 hz
    mixedMoment B raw25795step0 raw25795step0Labels = mixedMoment B raw25795step1 raw25795step1Labels := by
      have ha : raw25795step1 = (fun i j => raw25795step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25795step1 raw25795step0; decide +kernel
      have hl : raw25795step1Labels = raw25795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25795step0 raw25795step0Labels permutation44 permutation3
    mixedMoment B raw25795step1 raw25795step1Labels = mixedMoment B raw25795step2 raw25795step2Labels := by
      have ha : raw25795step2 = raw25795step1 := by apply Matrix.ext; unfold raw25795step2 raw25795step1; decide +kernel
      have hl : raw25795step1Labels = labelEmbedding6 ∘ raw25795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25795step1 raw25795step1Labels raw25795step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw25796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25796 raw25796Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25796 raw25796Labels = mixedMoment B raw25796step0 raw25796step0Labels := by
      have hz : ∀ j, raw25796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25796step0 = (fun i j => raw25796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25796step0 raw25796; decide +kernel
      have hl : raw25796step0Labels = raw25796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25796 raw25796Labels permutation346 hz
    mixedMoment B raw25796step0 raw25796step0Labels = mixedMoment B raw25796step1 raw25796step1Labels := by
      have ha : raw25796step1 = (fun i j => raw25796step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25796step1 raw25796step0; decide +kernel
      have hl : raw25796step1Labels = raw25796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25796step0 raw25796step0Labels permutation48 permutation3
    mixedMoment B raw25796step1 raw25796step1Labels = mixedMoment B raw25796step2 raw25796step2Labels := by
      have ha : raw25796step2 = raw25796step1 := by apply Matrix.ext; unfold raw25796step2 raw25796step1; decide +kernel
      have hl : raw25796step1Labels = labelEmbedding6 ∘ raw25796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25796step1 raw25796step1Labels raw25796step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25797 raw25797Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw25797 raw25797Labels = mixedMoment B raw25797step0 raw25797step0Labels := by
      have hz : ∀ j, raw25797 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25797step0 = (fun i j => raw25797 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25797step0 raw25797; decide +kernel
      have hl : raw25797step0Labels = raw25797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25797 raw25797Labels permutation265 hz
    mixedMoment B raw25797step0 raw25797step0Labels = mixedMoment B raw25797step1 raw25797step1Labels := by
      have ha : raw25797step1 = (fun i j => raw25797step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25797step1 raw25797step0; decide +kernel
      have hl : raw25797step1Labels = raw25797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25797step0 raw25797step0Labels permutation44 permutation3
    mixedMoment B raw25797step1 raw25797step1Labels = mixedMoment B raw25797step2 raw25797step2Labels := by
      have ha : raw25797step2 = raw25797step1 := by apply Matrix.ext; unfold raw25797step2 raw25797step1; decide +kernel
      have hl : raw25797step1Labels = labelEmbedding6 ∘ raw25797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25797step1 raw25797step1Labels raw25797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw25798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25798 raw25798Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw25798 raw25798Labels = mixedMoment B raw25798step0 raw25798step0Labels := by
      have ha : raw25798step0 = (fun i j => raw25798 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25798step0 raw25798; decide +kernel
      have hl : raw25798step0Labels = raw25798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25798 raw25798Labels permutation164 permutation3
    mixedMoment B raw25798step0 raw25798step0Labels = mixedMoment B raw25798step1 raw25798step1Labels := by
      have ha : raw25798step1 = raw25798step0 := by apply Matrix.ext; unfold raw25798step1 raw25798step0; decide +kernel
      have hl : raw25798step0Labels = labelEmbedding6 ∘ raw25798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25798step0 raw25798step0Labels raw25798step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw25799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25799 raw25799Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw25799 raw25799Labels = mixedMoment B raw25799step0 raw25799step0Labels := by
      have hz : ∀ j, raw25799 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25799step0 = (fun i j => raw25799 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25799step0 raw25799; decide +kernel
      have hl : raw25799step0Labels = raw25799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25799 raw25799Labels permutation265 hz
    mixedMoment B raw25799step0 raw25799step0Labels = mixedMoment B raw25799step1 raw25799step1Labels := by
      have ha : raw25799step1 = (fun i j => raw25799step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25799step1 raw25799step0; decide +kernel
      have hl : raw25799step1Labels = raw25799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25799step0 raw25799step0Labels permutation44 permutation3
    mixedMoment B raw25799step1 raw25799step1Labels = mixedMoment B raw25799step2 raw25799step2Labels := by
      have ha : raw25799step2 = raw25799step1 := by apply Matrix.ext; unfold raw25799step2 raw25799step1; decide +kernel
      have hl : raw25799step1Labels = labelEmbedding6 ∘ raw25799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25799step1 raw25799step1Labels raw25799step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw25800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25800 raw25800Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25800 raw25800Labels = mixedMoment B raw25800step0 raw25800step0Labels := by
      have hz : ∀ j, raw25800 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25800step0 = (fun i j => raw25800 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25800step0 raw25800; decide +kernel
      have hl : raw25800step0Labels = raw25800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25800 raw25800Labels permutation265 hz
    mixedMoment B raw25800step0 raw25800step0Labels = mixedMoment B raw25800step1 raw25800step1Labels := by
      have ha : raw25800step1 = (fun i j => raw25800step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25800step1 raw25800step0; decide +kernel
      have hl : raw25800step1Labels = raw25800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25800step0 raw25800step0Labels permutation48 permutation3
    mixedMoment B raw25800step1 raw25800step1Labels = mixedMoment B raw25800step2 raw25800step2Labels := by
      have ha : raw25800step2 = raw25800step1 := by apply Matrix.ext; unfold raw25800step2 raw25800step1; decide +kernel
      have hl : raw25800step1Labels = labelEmbedding6 ∘ raw25800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25800step1 raw25800step1Labels raw25800step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25801step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25801 raw25801Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw25801 raw25801Labels = mixedMoment B raw25801step0 raw25801step0Labels := by
      have hz : ∀ j, raw25801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25801step0 = (fun i j => raw25801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25801step0 raw25801; decide +kernel
      have hl : raw25801step0Labels = raw25801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25801 raw25801Labels permutation346 hz
    mixedMoment B raw25801step0 raw25801step0Labels = mixedMoment B raw25801step1 raw25801step1Labels := by
      have hz : ∀ j, raw25801step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25801step1 = (fun i j => raw25801step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25801step1 raw25801step0; decide +kernel
      have hl : raw25801step1Labels = raw25801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25801step0 raw25801step0Labels permutation56 hz
    mixedMoment B raw25801step1 raw25801step1Labels = mixedMoment B raw25801step2 raw25801step2Labels := by
      have ha : raw25801step2 = (fun i j => raw25801step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25801step2 raw25801step1; decide +kernel
      have hl : raw25801step2Labels = raw25801step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25801step1 raw25801step1Labels permutation11 permutation3
    mixedMoment B raw25801step2 raw25801step2Labels = mixedMoment B raw25801step3 raw25801step3Labels := by
      have ha : raw25801step3 = raw25801step2 := by apply Matrix.ext; unfold raw25801step3 raw25801step2; decide +kernel
      have hl : raw25801step2Labels = labelEmbedding6 ∘ raw25801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25801step2 raw25801step2Labels raw25801step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw25802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25802 raw25802Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw25802 raw25802Labels = mixedMoment B raw25802step0 raw25802step0Labels := by
      have hz : ∀ j, raw25802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25802step0 = (fun i j => raw25802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25802step0 raw25802; decide +kernel
      have hl : raw25802step0Labels = raw25802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25802 raw25802Labels permutation346 hz
    mixedMoment B raw25802step0 raw25802step0Labels = mixedMoment B raw25802step1 raw25802step1Labels := by
      have ha : raw25802step1 = (fun i j => raw25802step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25802step1 raw25802step0; decide +kernel
      have hl : raw25802step1Labels = raw25802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25802step0 raw25802step0Labels permutation35 permutation3
    mixedMoment B raw25802step1 raw25802step1Labels = mixedMoment B raw25802step2 raw25802step2Labels := by
      have ha : raw25802step2 = raw25802step1 := by apply Matrix.ext; unfold raw25802step2 raw25802step1; decide +kernel
      have hl : raw25802step1Labels = labelEmbedding6 ∘ raw25802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25802step1 raw25802step1Labels raw25802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw25803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25803 raw25803Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw25803 raw25803Labels = mixedMoment B raw25803step0 raw25803step0Labels := by
      have hz : ∀ j, raw25803 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25803step0 = (fun i j => raw25803 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25803step0 raw25803; decide +kernel
      have hl : raw25803step0Labels = raw25803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25803 raw25803Labels permutation265 hz
    mixedMoment B raw25803step0 raw25803step0Labels = mixedMoment B raw25803step1 raw25803step1Labels := by
      have ha : raw25803step1 = (fun i j => raw25803step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25803step1 raw25803step0; decide +kernel
      have hl : raw25803step1Labels = raw25803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25803step0 raw25803step0Labels permutation35 permutation3
    mixedMoment B raw25803step1 raw25803step1Labels = mixedMoment B raw25803step2 raw25803step2Labels := by
      have ha : raw25803step2 = raw25803step1 := by apply Matrix.ext; unfold raw25803step2 raw25803step1; decide +kernel
      have hl : raw25803step1Labels = labelEmbedding6 ∘ raw25803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25803step1 raw25803step1Labels raw25803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw25804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25804step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25804step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25804 raw25804Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw25804 raw25804Labels = mixedMoment B raw25804step0 raw25804step0Labels := by
      have hz : ∀ j, raw25804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25804step0 = (fun i j => raw25804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25804step0 raw25804; decide +kernel
      have hl : raw25804step0Labels = raw25804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25804 raw25804Labels permutation346 hz
    mixedMoment B raw25804step0 raw25804step0Labels = mixedMoment B raw25804step1 raw25804step1Labels := by
      have hz : ∀ j, raw25804step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25804step1 = (fun i j => raw25804step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25804step1 raw25804step0; decide +kernel
      have hl : raw25804step1Labels = raw25804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25804step0 raw25804step0Labels permutation56 hz
    mixedMoment B raw25804step1 raw25804step1Labels = mixedMoment B raw25804step2 raw25804step2Labels := by
      have ha : raw25804step2 = (fun i j => raw25804step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25804step2 raw25804step1; decide +kernel
      have hl : raw25804step2Labels = raw25804step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25804step1 raw25804step1Labels permutation11 permutation3
    mixedMoment B raw25804step2 raw25804step2Labels = mixedMoment B raw25804step3 raw25804step3Labels := by
      have ha : raw25804step3 = raw25804step2 := by apply Matrix.ext; unfold raw25804step3 raw25804step2; decide +kernel
      have hl : raw25804step2Labels = labelEmbedding6 ∘ raw25804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25804step2 raw25804step2Labels raw25804step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw25805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25805 raw25805Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw25805 raw25805Labels = mixedMoment B raw25805step0 raw25805step0Labels := by
      have hz : ∀ j, raw25805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25805step0 = (fun i j => raw25805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25805step0 raw25805; decide +kernel
      have hl : raw25805step0Labels = raw25805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25805 raw25805Labels permutation346 hz
    mixedMoment B raw25805step0 raw25805step0Labels = mixedMoment B raw25805step1 raw25805step1Labels := by
      have hz : ∀ j, raw25805step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25805step1 = (fun i j => raw25805step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25805step1 raw25805step0; decide +kernel
      have hl : raw25805step1Labels = raw25805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25805step0 raw25805step0Labels permutation56 hz
    mixedMoment B raw25805step1 raw25805step1Labels = mixedMoment B raw25805step2 raw25805step2Labels := by
      have ha : raw25805step2 = (fun i j => raw25805step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25805step2 raw25805step1; decide +kernel
      have hl : raw25805step2Labels = raw25805step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25805step1 raw25805step1Labels permutation11 permutation3
    mixedMoment B raw25805step2 raw25805step2Labels = mixedMoment B raw25805step3 raw25805step3Labels := by
      have ha : raw25805step3 = raw25805step2 := by apply Matrix.ext; unfold raw25805step3 raw25805step2; decide +kernel
      have hl : raw25805step2Labels = labelEmbedding6 ∘ raw25805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25805step2 raw25805step2Labels raw25805step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw25806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25806 raw25806Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw25806 raw25806Labels = mixedMoment B raw25806step0 raw25806step0Labels := by
      have hz : ∀ j, raw25806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25806step0 = (fun i j => raw25806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25806step0 raw25806; decide +kernel
      have hl : raw25806step0Labels = raw25806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25806 raw25806Labels permutation346 hz
    mixedMoment B raw25806step0 raw25806step0Labels = mixedMoment B raw25806step1 raw25806step1Labels := by
      have hz : ∀ j, raw25806step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25806step1 = (fun i j => raw25806step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25806step1 raw25806step0; decide +kernel
      have hl : raw25806step1Labels = raw25806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25806step0 raw25806step0Labels permutation56 hz
    mixedMoment B raw25806step1 raw25806step1Labels = mixedMoment B raw25806step2 raw25806step2Labels := by
      have ha : raw25806step2 = (fun i j => raw25806step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25806step2 raw25806step1; decide +kernel
      have hl : raw25806step2Labels = raw25806step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25806step1 raw25806step1Labels permutation8 permutation3
    mixedMoment B raw25806step2 raw25806step2Labels = mixedMoment B raw25806step3 raw25806step3Labels := by
      have ha : raw25806step3 = raw25806step2 := by apply Matrix.ext; unfold raw25806step3 raw25806step2; decide +kernel
      have hl : raw25806step2Labels = labelEmbedding6 ∘ raw25806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25806step2 raw25806step2Labels raw25806step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4133 node4133Labels := by rfl

def raw25807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25807 raw25807Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw25807 raw25807Labels = mixedMoment B raw25807step0 raw25807step0Labels := by
      have hz : ∀ j, raw25807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25807step0 = (fun i j => raw25807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25807step0 raw25807; decide +kernel
      have hl : raw25807step0Labels = raw25807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25807 raw25807Labels permutation346 hz
    mixedMoment B raw25807step0 raw25807step0Labels = mixedMoment B raw25807step1 raw25807step1Labels := by
      have ha : raw25807step1 = (fun i j => raw25807step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25807step1 raw25807step0; decide +kernel
      have hl : raw25807step1Labels = raw25807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25807step0 raw25807step0Labels permutation32 permutation3
    mixedMoment B raw25807step1 raw25807step1Labels = mixedMoment B raw25807step2 raw25807step2Labels := by
      have ha : raw25807step2 = raw25807step1 := by apply Matrix.ext; unfold raw25807step2 raw25807step1; decide +kernel
      have hl : raw25807step1Labels = labelEmbedding6 ∘ raw25807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25807step1 raw25807step1Labels raw25807step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw25808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25808 raw25808Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw25808 raw25808Labels = mixedMoment B raw25808step0 raw25808step0Labels := by
      have hz : ∀ j, raw25808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25808step0 = (fun i j => raw25808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25808step0 raw25808; decide +kernel
      have hl : raw25808step0Labels = raw25808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25808 raw25808Labels permutation265 hz
    mixedMoment B raw25808step0 raw25808step0Labels = mixedMoment B raw25808step1 raw25808step1Labels := by
      have ha : raw25808step1 = (fun i j => raw25808step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25808step1 raw25808step0; decide +kernel
      have hl : raw25808step1Labels = raw25808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25808step0 raw25808step0Labels permutation32 permutation3
    mixedMoment B raw25808step1 raw25808step1Labels = mixedMoment B raw25808step2 raw25808step2Labels := by
      have ha : raw25808step2 = raw25808step1 := by apply Matrix.ext; unfold raw25808step2 raw25808step1; decide +kernel
      have hl : raw25808step1Labels = labelEmbedding6 ∘ raw25808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25808step1 raw25808step1Labels raw25808step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw25809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25809step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25809 raw25809Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25809 raw25809Labels = mixedMoment B raw25809step0 raw25809step0Labels := by
      have hz : ∀ j, raw25809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25809step0 = (fun i j => raw25809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25809step0 raw25809; decide +kernel
      have hl : raw25809step0Labels = raw25809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25809 raw25809Labels permutation346 hz
    mixedMoment B raw25809step0 raw25809step0Labels = mixedMoment B raw25809step1 raw25809step1Labels := by
      have hz : ∀ j, raw25809step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25809step1 = (fun i j => raw25809step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25809step1 raw25809step0; decide +kernel
      have hl : raw25809step1Labels = raw25809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25809step0 raw25809step0Labels permutation56 hz
    mixedMoment B raw25809step1 raw25809step1Labels = mixedMoment B raw25809step2 raw25809step2Labels := by
      have ha : raw25809step2 = (fun i j => raw25809step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25809step2 raw25809step1; decide +kernel
      have hl : raw25809step2Labels = raw25809step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25809step1 raw25809step1Labels permutation12 permutation3
    mixedMoment B raw25809step2 raw25809step2Labels = mixedMoment B raw25809step3 raw25809step3Labels := by
      have ha : raw25809step3 = raw25809step2 := by apply Matrix.ext; unfold raw25809step3 raw25809step2; decide +kernel
      have hl : raw25809step2Labels = labelEmbedding6 ∘ raw25809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25809step2 raw25809step2Labels raw25809step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25810 raw25810Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw25810 raw25810Labels = mixedMoment B raw25810step0 raw25810step0Labels := by
      have hz : ∀ j, raw25810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25810step0 = (fun i j => raw25810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25810step0 raw25810; decide +kernel
      have hl : raw25810step0Labels = raw25810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25810 raw25810Labels permutation346 hz
    mixedMoment B raw25810step0 raw25810step0Labels = mixedMoment B raw25810step1 raw25810step1Labels := by
      have hz : ∀ j, raw25810step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25810step1 = (fun i j => raw25810step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25810step1 raw25810step0; decide +kernel
      have hl : raw25810step1Labels = raw25810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25810step0 raw25810step0Labels permutation56 hz
    mixedMoment B raw25810step1 raw25810step1Labels = mixedMoment B raw25810step2 raw25810step2Labels := by
      have ha : raw25810step2 = (fun i j => raw25810step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25810step2 raw25810step1; decide +kernel
      have hl : raw25810step2Labels = raw25810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25810step1 raw25810step1Labels permutation10 permutation3
    mixedMoment B raw25810step2 raw25810step2Labels = mixedMoment B raw25810step3 raw25810step3Labels := by
      have ha : raw25810step3 = raw25810step2 := by apply Matrix.ext; unfold raw25810step3 raw25810step2; decide +kernel
      have hl : raw25810step2Labels = labelEmbedding6 ∘ raw25810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25810step2 raw25810step2Labels raw25810step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw25811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25811 raw25811Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw25811 raw25811Labels = mixedMoment B raw25811step0 raw25811step0Labels := by
      have hz : ∀ j, raw25811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25811step0 = (fun i j => raw25811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25811step0 raw25811; decide +kernel
      have hl : raw25811step0Labels = raw25811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25811 raw25811Labels permutation346 hz
    mixedMoment B raw25811step0 raw25811step0Labels = mixedMoment B raw25811step1 raw25811step1Labels := by
      have ha : raw25811step1 = (fun i j => raw25811step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25811step1 raw25811step0; decide +kernel
      have hl : raw25811step1Labels = raw25811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25811step0 raw25811step0Labels permutation34 permutation3
    mixedMoment B raw25811step1 raw25811step1Labels = mixedMoment B raw25811step2 raw25811step2Labels := by
      have ha : raw25811step2 = raw25811step1 := by apply Matrix.ext; unfold raw25811step2 raw25811step1; decide +kernel
      have hl : raw25811step1Labels = labelEmbedding6 ∘ raw25811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25811step1 raw25811step1Labels raw25811step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw25812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25812 raw25812Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw25812 raw25812Labels = mixedMoment B raw25812step0 raw25812step0Labels := by
      have hz : ∀ j, raw25812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25812step0 = (fun i j => raw25812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25812step0 raw25812; decide +kernel
      have hl : raw25812step0Labels = raw25812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25812 raw25812Labels permutation265 hz
    mixedMoment B raw25812step0 raw25812step0Labels = mixedMoment B raw25812step1 raw25812step1Labels := by
      have ha : raw25812step1 = (fun i j => raw25812step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25812step1 raw25812step0; decide +kernel
      have hl : raw25812step1Labels = raw25812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25812step0 raw25812step0Labels permutation34 permutation3
    mixedMoment B raw25812step1 raw25812step1Labels = mixedMoment B raw25812step2 raw25812step2Labels := by
      have ha : raw25812step2 = raw25812step1 := by apply Matrix.ext; unfold raw25812step2 raw25812step1; decide +kernel
      have hl : raw25812step1Labels = labelEmbedding6 ∘ raw25812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25812step1 raw25812step1Labels raw25812step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw25813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25813 raw25813Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw25813 raw25813Labels = mixedMoment B raw25813step0 raw25813step0Labels := by
      have hz : ∀ j, raw25813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25813step0 = (fun i j => raw25813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25813step0 raw25813; decide +kernel
      have hl : raw25813step0Labels = raw25813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25813 raw25813Labels permutation346 hz
    mixedMoment B raw25813step0 raw25813step0Labels = mixedMoment B raw25813step1 raw25813step1Labels := by
      have hz : ∀ j, raw25813step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25813step1 = (fun i j => raw25813step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25813step1 raw25813step0; decide +kernel
      have hl : raw25813step1Labels = raw25813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25813step0 raw25813step0Labels permutation56 hz
    mixedMoment B raw25813step1 raw25813step1Labels = mixedMoment B raw25813step2 raw25813step2Labels := by
      have ha : raw25813step2 = (fun i j => raw25813step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25813step2 raw25813step1; decide +kernel
      have hl : raw25813step2Labels = raw25813step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25813step1 raw25813step1Labels permutation10 permutation3
    mixedMoment B raw25813step2 raw25813step2Labels = mixedMoment B raw25813step3 raw25813step3Labels := by
      have ha : raw25813step3 = raw25813step2 := by apply Matrix.ext; unfold raw25813step3 raw25813step2; decide +kernel
      have hl : raw25813step2Labels = labelEmbedding6 ∘ raw25813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25813step2 raw25813step2Labels raw25813step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw25814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25814 raw25814Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw25814 raw25814Labels = mixedMoment B raw25814step0 raw25814step0Labels := by
      have hz : ∀ j, raw25814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25814step0 = (fun i j => raw25814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25814step0 raw25814; decide +kernel
      have hl : raw25814step0Labels = raw25814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25814 raw25814Labels permutation346 hz
    mixedMoment B raw25814step0 raw25814step0Labels = mixedMoment B raw25814step1 raw25814step1Labels := by
      have hz : ∀ j, raw25814step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25814step1 = (fun i j => raw25814step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25814step1 raw25814step0; decide +kernel
      have hl : raw25814step1Labels = raw25814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25814step0 raw25814step0Labels permutation56 hz
    mixedMoment B raw25814step1 raw25814step1Labels = mixedMoment B raw25814step2 raw25814step2Labels := by
      have ha : raw25814step2 = (fun i j => raw25814step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25814step2 raw25814step1; decide +kernel
      have hl : raw25814step2Labels = raw25814step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25814step1 raw25814step1Labels permutation8 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw25815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25815 raw25815Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw25815 raw25815Labels = mixedMoment B raw25815step0 raw25815step0Labels := by
      have hz : ∀ j, raw25815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25815step0 = (fun i j => raw25815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25815step0 raw25815; decide +kernel
      have hl : raw25815step0Labels = raw25815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25815 raw25815Labels permutation346 hz
    mixedMoment B raw25815step0 raw25815step0Labels = mixedMoment B raw25815step1 raw25815step1Labels := by
      have ha : raw25815step1 = (fun i j => raw25815step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25815step1 raw25815step0; decide +kernel
      have hl : raw25815step1Labels = raw25815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25815step0 raw25815step0Labels permutation44 permutation3
    _ = mixedMoment B node554 node554Labels := by rfl

def raw25816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25816 raw25816Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw25816 raw25816Labels = mixedMoment B raw25816step0 raw25816step0Labels := by
      have ha : raw25816step0 = (fun i j => raw25816 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25816step0 raw25816; decide +kernel
      have hl : raw25816step0Labels = raw25816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25816 raw25816Labels permutation188 permutation3
    _ = mixedMoment B node879 node879Labels := by rfl

def raw25817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25817 raw25817Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw25817 raw25817Labels = mixedMoment B raw25817step0 raw25817step0Labels := by
      have hz : ∀ j, raw25817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25817step0 = (fun i j => raw25817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25817step0 raw25817; decide +kernel
      have hl : raw25817step0Labels = raw25817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25817 raw25817Labels permutation346 hz
    mixedMoment B raw25817step0 raw25817step0Labels = mixedMoment B raw25817step1 raw25817step1Labels := by
      have ha : raw25817step1 = (fun i j => raw25817step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25817step1 raw25817step0; decide +kernel
      have hl : raw25817step1Labels = raw25817step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25817step0 raw25817step0Labels permutation44 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw25818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25818step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25818 raw25818Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25818 raw25818Labels = mixedMoment B raw25818step0 raw25818step0Labels := by
      have hz : ∀ j, raw25818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25818step0 = (fun i j => raw25818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25818step0 raw25818; decide +kernel
      have hl : raw25818step0Labels = raw25818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25818 raw25818Labels permutation346 hz
    mixedMoment B raw25818step0 raw25818step0Labels = mixedMoment B raw25818step1 raw25818step1Labels := by
      have ha : raw25818step1 = (fun i j => raw25818step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25818step1 raw25818step0; decide +kernel
      have hl : raw25818step1Labels = raw25818step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25818step0 raw25818step0Labels permutation48 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw25819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25819step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25819 raw25819Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw25819 raw25819Labels = mixedMoment B raw25819step0 raw25819step0Labels := by
      have hz : ∀ j, raw25819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25819step0 = (fun i j => raw25819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25819step0 raw25819; decide +kernel
      have hl : raw25819step0Labels = raw25819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25819 raw25819Labels permutation265 hz
    mixedMoment B raw25819step0 raw25819step0Labels = mixedMoment B raw25819step1 raw25819step1Labels := by
      have ha : raw25819step1 = (fun i j => raw25819step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25819step1 raw25819step0; decide +kernel
      have hl : raw25819step1Labels = raw25819step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25819step0 raw25819step0Labels permutation44 permutation3
    _ = mixedMoment B node554 node554Labels := by rfl

def raw25820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25820 raw25820Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw25820 raw25820Labels = mixedMoment B raw25820step0 raw25820step0Labels := by
      have ha : raw25820step0 = (fun i j => raw25820 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25820step0 raw25820; decide +kernel
      have hl : raw25820step0Labels = raw25820Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25820 raw25820Labels permutation164 permutation3
    _ = mixedMoment B node879 node879Labels := by rfl

def raw25821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25821 raw25821Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw25821 raw25821Labels = mixedMoment B raw25821step0 raw25821step0Labels := by
      have hz : ∀ j, raw25821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25821step0 = (fun i j => raw25821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25821step0 raw25821; decide +kernel
      have hl : raw25821step0Labels = raw25821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25821 raw25821Labels permutation265 hz
    mixedMoment B raw25821step0 raw25821step0Labels = mixedMoment B raw25821step1 raw25821step1Labels := by
      have ha : raw25821step1 = (fun i j => raw25821step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25821step1 raw25821step0; decide +kernel
      have hl : raw25821step1Labels = raw25821step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25821step0 raw25821step0Labels permutation44 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw25822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25822 raw25822Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25822 raw25822Labels = mixedMoment B raw25822step0 raw25822step0Labels := by
      have hz : ∀ j, raw25822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25822step0 = (fun i j => raw25822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25822step0 raw25822; decide +kernel
      have hl : raw25822step0Labels = raw25822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25822 raw25822Labels permutation265 hz
    mixedMoment B raw25822step0 raw25822step0Labels = mixedMoment B raw25822step1 raw25822step1Labels := by
      have ha : raw25822step1 = (fun i j => raw25822step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25822step1 raw25822step0; decide +kernel
      have hl : raw25822step1Labels = raw25822step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25822step0 raw25822step0Labels permutation48 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw25823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25823step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25823 raw25823Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw25823 raw25823Labels = mixedMoment B raw25823step0 raw25823step0Labels := by
      have hz : ∀ j, raw25823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25823step0 = (fun i j => raw25823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25823step0 raw25823; decide +kernel
      have hl : raw25823step0Labels = raw25823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25823 raw25823Labels permutation346 hz
    mixedMoment B raw25823step0 raw25823step0Labels = mixedMoment B raw25823step1 raw25823step1Labels := by
      have hz : ∀ j, raw25823step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25823step1 = (fun i j => raw25823step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25823step1 raw25823step0; decide +kernel
      have hl : raw25823step1Labels = raw25823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25823step0 raw25823step0Labels permutation56 hz
    mixedMoment B raw25823step1 raw25823step1Labels = mixedMoment B raw25823step2 raw25823step2Labels := by
      have ha : raw25823step2 = (fun i j => raw25823step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25823step2 raw25823step1; decide +kernel
      have hl : raw25823step2Labels = raw25823step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25823step1 raw25823step1Labels permutation11 permutation3
    _ = mixedMoment B node556 node556Labels := by rfl

def raw25824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25824 raw25824Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw25824 raw25824Labels = mixedMoment B raw25824step0 raw25824step0Labels := by
      have hz : ∀ j, raw25824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25824step0 = (fun i j => raw25824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25824step0 raw25824; decide +kernel
      have hl : raw25824step0Labels = raw25824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25824 raw25824Labels permutation346 hz
    mixedMoment B raw25824step0 raw25824step0Labels = mixedMoment B raw25824step1 raw25824step1Labels := by
      have ha : raw25824step1 = (fun i j => raw25824step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25824step1 raw25824step0; decide +kernel
      have hl : raw25824step1Labels = raw25824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25824step0 raw25824step0Labels permutation35 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw25825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw25825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25825 raw25825Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw25825 raw25825Labels = mixedMoment B raw25825step0 raw25825step0Labels := by
      have hz : ∀ j, raw25825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25825step0 = (fun i j => raw25825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25825step0 raw25825; decide +kernel
      have hl : raw25825step0Labels = raw25825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25825 raw25825Labels permutation265 hz
    mixedMoment B raw25825step0 raw25825step0Labels = mixedMoment B raw25825step1 raw25825step1Labels := by
      have ha : raw25825step1 = (fun i j => raw25825step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25825step1 raw25825step0; decide +kernel
      have hl : raw25825step1Labels = raw25825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25825step0 raw25825step0Labels permutation35 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw25826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw25826step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw25826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25826 raw25826Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw25826 raw25826Labels = mixedMoment B raw25826step0 raw25826step0Labels := by
      have hz : ∀ j, raw25826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25826step0 = (fun i j => raw25826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25826step0 raw25826; decide +kernel
      have hl : raw25826step0Labels = raw25826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25826 raw25826Labels permutation346 hz
    mixedMoment B raw25826step0 raw25826step0Labels = mixedMoment B raw25826step1 raw25826step1Labels := by
      have hz : ∀ j, raw25826step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25826step1 = (fun i j => raw25826step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25826step1 raw25826step0; decide +kernel
      have hl : raw25826step1Labels = raw25826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25826step0 raw25826step0Labels permutation56 hz
    mixedMoment B raw25826step1 raw25826step1Labels = mixedMoment B raw25826step2 raw25826step2Labels := by
      have ha : raw25826step2 = (fun i j => raw25826step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25826step2 raw25826step1; decide +kernel
      have hl : raw25826step2Labels = raw25826step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25826step1 raw25826step1Labels permutation11 permutation3
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw25827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25827step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25827 raw25827Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw25827 raw25827Labels = mixedMoment B raw25827step0 raw25827step0Labels := by
      have hz : ∀ j, raw25827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25827step0 = (fun i j => raw25827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25827step0 raw25827; decide +kernel
      have hl : raw25827step0Labels = raw25827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25827 raw25827Labels permutation346 hz
    mixedMoment B raw25827step0 raw25827step0Labels = mixedMoment B raw25827step1 raw25827step1Labels := by
      have hz : ∀ j, raw25827step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25827step1 = (fun i j => raw25827step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25827step1 raw25827step0; decide +kernel
      have hl : raw25827step1Labels = raw25827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25827step0 raw25827step0Labels permutation56 hz
    mixedMoment B raw25827step1 raw25827step1Labels = mixedMoment B raw25827step2 raw25827step2Labels := by
      have ha : raw25827step2 = (fun i j => raw25827step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25827step2 raw25827step1; decide +kernel
      have hl : raw25827step2Labels = raw25827step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25827step1 raw25827step1Labels permutation11 permutation3
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw25828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25828step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25828step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25828 raw25828Labels = mixedMoment B node563 node563Labels := by
  calc
    mixedMoment B raw25828 raw25828Labels = mixedMoment B raw25828step0 raw25828step0Labels := by
      have hz : ∀ j, raw25828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25828step0 = (fun i j => raw25828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25828step0 raw25828; decide +kernel
      have hl : raw25828step0Labels = raw25828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25828 raw25828Labels permutation346 hz
    mixedMoment B raw25828step0 raw25828step0Labels = mixedMoment B raw25828step1 raw25828step1Labels := by
      have hz : ∀ j, raw25828step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25828step1 = (fun i j => raw25828step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25828step1 raw25828step0; decide +kernel
      have hl : raw25828step1Labels = raw25828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25828step0 raw25828step0Labels permutation56 hz
    mixedMoment B raw25828step1 raw25828step1Labels = mixedMoment B raw25828step2 raw25828step2Labels := by
      have ha : raw25828step2 = (fun i j => raw25828step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25828step2 raw25828step1; decide +kernel
      have hl : raw25828step2Labels = raw25828step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25828step1 raw25828step1Labels permutation8 permutation3
    _ = mixedMoment B node563 node563Labels := by rfl

def raw25829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25829 raw25829Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw25829 raw25829Labels = mixedMoment B raw25829step0 raw25829step0Labels := by
      have hz : ∀ j, raw25829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25829step0 = (fun i j => raw25829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25829step0 raw25829; decide +kernel
      have hl : raw25829step0Labels = raw25829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25829 raw25829Labels permutation346 hz
    mixedMoment B raw25829step0 raw25829step0Labels = mixedMoment B raw25829step1 raw25829step1Labels := by
      have ha : raw25829step1 = (fun i j => raw25829step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25829step1 raw25829step0; decide +kernel
      have hl : raw25829step1Labels = raw25829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25829step0 raw25829step0Labels permutation32 permutation3
    _ = mixedMoment B node892 node892Labels := by rfl

def raw25830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw25830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25830 raw25830Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw25830 raw25830Labels = mixedMoment B raw25830step0 raw25830step0Labels := by
      have hz : ∀ j, raw25830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25830step0 = (fun i j => raw25830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25830step0 raw25830; decide +kernel
      have hl : raw25830step0Labels = raw25830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25830 raw25830Labels permutation265 hz
    mixedMoment B raw25830step0 raw25830step0Labels = mixedMoment B raw25830step1 raw25830step1Labels := by
      have ha : raw25830step1 = (fun i j => raw25830step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25830step1 raw25830step0; decide +kernel
      have hl : raw25830step1Labels = raw25830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25830step0 raw25830step0Labels permutation32 permutation3
    _ = mixedMoment B node892 node892Labels := by rfl

def raw25831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw25831step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25831 raw25831Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw25831 raw25831Labels = mixedMoment B raw25831step0 raw25831step0Labels := by
      have hz : ∀ j, raw25831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25831step0 = (fun i j => raw25831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25831step0 raw25831; decide +kernel
      have hl : raw25831step0Labels = raw25831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25831 raw25831Labels permutation346 hz
    mixedMoment B raw25831step0 raw25831step0Labels = mixedMoment B raw25831step1 raw25831step1Labels := by
      have hz : ∀ j, raw25831step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25831step1 = (fun i j => raw25831step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25831step1 raw25831step0; decide +kernel
      have hl : raw25831step1Labels = raw25831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25831step0 raw25831step0Labels permutation56 hz
    mixedMoment B raw25831step1 raw25831step1Labels = mixedMoment B raw25831step2 raw25831step2Labels := by
      have ha : raw25831step2 = (fun i j => raw25831step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25831step2 raw25831step1; decide +kernel
      have hl : raw25831step2Labels = raw25831step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25831step1 raw25831step1Labels permutation12 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw25832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25832 raw25832Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw25832 raw25832Labels = mixedMoment B raw25832step0 raw25832step0Labels := by
      have hz : ∀ j, raw25832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25832step0 = (fun i j => raw25832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25832step0 raw25832; decide +kernel
      have hl : raw25832step0Labels = raw25832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25832 raw25832Labels permutation346 hz
    mixedMoment B raw25832step0 raw25832step0Labels = mixedMoment B raw25832step1 raw25832step1Labels := by
      have hz : ∀ j, raw25832step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25832step1 = (fun i j => raw25832step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25832step1 raw25832step0; decide +kernel
      have hl : raw25832step1Labels = raw25832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25832step0 raw25832step0Labels permutation56 hz
    mixedMoment B raw25832step1 raw25832step1Labels = mixedMoment B raw25832step2 raw25832step2Labels := by
      have ha : raw25832step2 = (fun i j => raw25832step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25832step2 raw25832step1; decide +kernel
      have hl : raw25832step2Labels = raw25832step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25832step1 raw25832step1Labels permutation10 permutation3
    _ = mixedMoment B node555 node555Labels := by rfl

def raw25833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25833 raw25833Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw25833 raw25833Labels = mixedMoment B raw25833step0 raw25833step0Labels := by
      have hz : ∀ j, raw25833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25833step0 = (fun i j => raw25833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25833step0 raw25833; decide +kernel
      have hl : raw25833step0Labels = raw25833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25833 raw25833Labels permutation346 hz
    mixedMoment B raw25833step0 raw25833step0Labels = mixedMoment B raw25833step1 raw25833step1Labels := by
      have ha : raw25833step1 = (fun i j => raw25833step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25833step1 raw25833step0; decide +kernel
      have hl : raw25833step1Labels = raw25833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25833step0 raw25833step0Labels permutation34 permutation3
    _ = mixedMoment B node881 node881Labels := by rfl

def raw25834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw25834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25834 raw25834Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw25834 raw25834Labels = mixedMoment B raw25834step0 raw25834step0Labels := by
      have hz : ∀ j, raw25834 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25834step0 = (fun i j => raw25834 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25834step0 raw25834; decide +kernel
      have hl : raw25834step0Labels = raw25834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25834 raw25834Labels permutation265 hz
    mixedMoment B raw25834step0 raw25834step0Labels = mixedMoment B raw25834step1 raw25834step1Labels := by
      have ha : raw25834step1 = (fun i j => raw25834step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25834step1 raw25834step0; decide +kernel
      have hl : raw25834step1Labels = raw25834step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25834step0 raw25834step0Labels permutation34 permutation3
    _ = mixedMoment B node881 node881Labels := by rfl

def raw25835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw25835step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw25835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25835 raw25835Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw25835 raw25835Labels = mixedMoment B raw25835step0 raw25835step0Labels := by
      have hz : ∀ j, raw25835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25835step0 = (fun i j => raw25835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25835step0 raw25835; decide +kernel
      have hl : raw25835step0Labels = raw25835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25835 raw25835Labels permutation346 hz
    mixedMoment B raw25835step0 raw25835step0Labels = mixedMoment B raw25835step1 raw25835step1Labels := by
      have hz : ∀ j, raw25835step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25835step1 = (fun i j => raw25835step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25835step1 raw25835step0; decide +kernel
      have hl : raw25835step1Labels = raw25835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25835step0 raw25835step0Labels permutation56 hz
    mixedMoment B raw25835step1 raw25835step1Labels = mixedMoment B raw25835step2 raw25835step2Labels := by
      have ha : raw25835step2 = (fun i j => raw25835step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25835step2 raw25835step1; decide +kernel
      have hl : raw25835step2Labels = raw25835step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25835step1 raw25835step1Labels permutation10 permutation3
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw25836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25836 raw25836Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw25836 raw25836Labels = mixedMoment B raw25836step0 raw25836step0Labels := by
      have hz : ∀ j, raw25836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25836step0 = (fun i j => raw25836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25836step0 raw25836; decide +kernel
      have hl : raw25836step0Labels = raw25836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25836 raw25836Labels permutation346 hz
    mixedMoment B raw25836step0 raw25836step0Labels = mixedMoment B raw25836step1 raw25836step1Labels := by
      have ha : raw25836step1 = (fun i j => raw25836step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25836step1 raw25836step0; decide +kernel
      have hl : raw25836step1Labels = raw25836step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25836step0 raw25836step0Labels permutation34 permutation6
    mixedMoment B raw25836step1 raw25836step1Labels = mixedMoment B raw25836step2 raw25836step2Labels := by
      have ha : raw25836step2 = raw25836step1 := by apply Matrix.ext; unfold raw25836step2 raw25836step1; decide +kernel
      have hl : raw25836step1Labels = labelEmbedding9 ∘ raw25836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25836step1 raw25836step1Labels raw25836step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw25837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25837 raw25837Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw25837 raw25837Labels = mixedMoment B raw25837step0 raw25837step0Labels := by
      have hz : ∀ j, raw25837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25837step0 = (fun i j => raw25837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25837step0 raw25837; decide +kernel
      have hl : raw25837step0Labels = raw25837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25837 raw25837Labels permutation346 hz
    mixedMoment B raw25837step0 raw25837step0Labels = mixedMoment B raw25837step1 raw25837step1Labels := by
      have hz : ∀ j, raw25837step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25837step1 = (fun i j => raw25837step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25837step1 raw25837step0; decide +kernel
      have hl : raw25837step1Labels = raw25837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25837step0 raw25837step0Labels permutation56 hz
    mixedMoment B raw25837step1 raw25837step1Labels = mixedMoment B raw25837step2 raw25837step2Labels := by
      have ha : raw25837step2 = (fun i j => raw25837step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25837step2 raw25837step1; decide +kernel
      have hl : raw25837step2Labels = raw25837step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25837step1 raw25837step1Labels permutation10 permutation6
    mixedMoment B raw25837step2 raw25837step2Labels = mixedMoment B raw25837step3 raw25837step3Labels := by
      have ha : raw25837step3 = raw25837step2 := by apply Matrix.ext; unfold raw25837step3 raw25837step2; decide +kernel
      have hl : raw25837step2Labels = labelEmbedding9 ∘ raw25837step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25837step2 raw25837step2Labels raw25837step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw25838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25838step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25838step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25838 raw25838Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw25838 raw25838Labels = mixedMoment B raw25838step0 raw25838step0Labels := by
      have hz : ∀ j, raw25838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25838step0 = (fun i j => raw25838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25838step0 raw25838; decide +kernel
      have hl : raw25838step0Labels = raw25838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25838 raw25838Labels permutation265 hz
    mixedMoment B raw25838step0 raw25838step0Labels = mixedMoment B raw25838step1 raw25838step1Labels := by
      have ha : raw25838step1 = (fun i j => raw25838step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25838step1 raw25838step0; decide +kernel
      have hl : raw25838step1Labels = raw25838step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25838step0 raw25838step0Labels permutation45 permutation4
    mixedMoment B raw25838step1 raw25838step1Labels = mixedMoment B raw25838step2 raw25838step2Labels := by
      have ha : raw25838step2 = -raw25838step1 := by apply Matrix.ext; change ∀ i j, raw25838step2 i j = -(raw25838step1 i j); unfold raw25838step2 raw25838step1; decide +kernel
      have hl : raw25838step2Labels = raw25838step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25838step2 raw25838step2Labels = mixedMoment B raw25838step3 raw25838step3Labels := by
      have ha : raw25838step3 = raw25838step2 := by apply Matrix.ext; unfold raw25838step3 raw25838step2; decide +kernel
      have hl : raw25838step2Labels = labelEmbedding7 ∘ raw25838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25838step2 raw25838step2Labels raw25838step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw25839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25839 raw25839Labels = mixedMoment B node4397 node4397Labels := by
  calc
    mixedMoment B raw25839 raw25839Labels = mixedMoment B raw25839step0 raw25839step0Labels := by
      have ha : raw25839step0 = (fun i j => raw25839 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25839step0 raw25839; decide +kernel
      have hl : raw25839step0Labels = raw25839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25839 raw25839Labels permutation154 permutation6
    mixedMoment B raw25839step0 raw25839step0Labels = mixedMoment B raw25839step1 raw25839step1Labels := by
      have ha : raw25839step1 = raw25839step0 := by apply Matrix.ext; unfold raw25839step1 raw25839step0; decide +kernel
      have hl : raw25839step0Labels = labelEmbedding9 ∘ raw25839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25839step0 raw25839step0Labels raw25839step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4397 node4397Labels := by rfl

def raw25840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25840 raw25840Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw25840 raw25840Labels = mixedMoment B raw25840step0 raw25840step0Labels := by
      have hz : ∀ j, raw25840 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25840step0 = (fun i j => raw25840 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25840step0 raw25840; decide +kernel
      have hl : raw25840step0Labels = raw25840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25840 raw25840Labels permutation265 hz
    mixedMoment B raw25840step0 raw25840step0Labels = mixedMoment B raw25840step1 raw25840step1Labels := by
      have ha : raw25840step1 = (fun i j => raw25840step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25840step1 raw25840step0; decide +kernel
      have hl : raw25840step1Labels = raw25840step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25840step0 raw25840step0Labels permutation34 permutation6
    mixedMoment B raw25840step1 raw25840step1Labels = mixedMoment B raw25840step2 raw25840step2Labels := by
      have ha : raw25840step2 = raw25840step1 := by apply Matrix.ext; unfold raw25840step2 raw25840step1; decide +kernel
      have hl : raw25840step1Labels = labelEmbedding9 ∘ raw25840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25840step1 raw25840step1Labels raw25840step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw25841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw25841step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25841step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw25841step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25841 raw25841Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw25841 raw25841Labels = mixedMoment B raw25841step0 raw25841step0Labels := by
      have hz : ∀ j, raw25841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25841step0 = (fun i j => raw25841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25841step0 raw25841; decide +kernel
      have hl : raw25841step0Labels = raw25841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25841 raw25841Labels permutation346 hz
    mixedMoment B raw25841step0 raw25841step0Labels = mixedMoment B raw25841step1 raw25841step1Labels := by
      have hz : ∀ j, raw25841step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25841step1 = (fun i j => raw25841step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25841step1 raw25841step0; decide +kernel
      have hl : raw25841step1Labels = raw25841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25841step0 raw25841step0Labels permutation56 hz
    mixedMoment B raw25841step1 raw25841step1Labels = mixedMoment B raw25841step2 raw25841step2Labels := by
      have ha : raw25841step2 = (fun i j => raw25841step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25841step2 raw25841step1; decide +kernel
      have hl : raw25841step2Labels = raw25841step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25841step1 raw25841step1Labels permutation11 permutation4
    mixedMoment B raw25841step2 raw25841step2Labels = mixedMoment B raw25841step3 raw25841step3Labels := by
      have ha : raw25841step3 = -raw25841step2 := by apply Matrix.ext; change ∀ i j, raw25841step3 i j = -(raw25841step2 i j); unfold raw25841step3 raw25841step2; decide +kernel
      have hl : raw25841step3Labels = raw25841step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25841step3 raw25841step3Labels = mixedMoment B raw25841step4 raw25841step4Labels := by
      have ha : raw25841step4 = raw25841step3 := by apply Matrix.ext; unfold raw25841step4 raw25841step3; decide +kernel
      have hl : raw25841step3Labels = labelEmbedding7 ∘ raw25841step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25841step3 raw25841step3Labels raw25841step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw25842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25842 raw25842Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw25842 raw25842Labels = mixedMoment B raw25842step0 raw25842step0Labels := by
      have hz : ∀ j, raw25842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25842step0 = (fun i j => raw25842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25842step0 raw25842; decide +kernel
      have hl : raw25842step0Labels = raw25842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25842 raw25842Labels permutation346 hz
    mixedMoment B raw25842step0 raw25842step0Labels = mixedMoment B raw25842step1 raw25842step1Labels := by
      have ha : raw25842step1 = (fun i j => raw25842step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25842step1 raw25842step0; decide +kernel
      have hl : raw25842step1Labels = raw25842step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25842step0 raw25842step0Labels permutation34 permutation6
    mixedMoment B raw25842step1 raw25842step1Labels = mixedMoment B raw25842step2 raw25842step2Labels := by
      have ha : raw25842step2 = raw25842step1 := by apply Matrix.ext; unfold raw25842step2 raw25842step1; decide +kernel
      have hl : raw25842step1Labels = labelEmbedding9 ∘ raw25842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25842step1 raw25842step1Labels raw25842step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw25843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw25843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25843 raw25843Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw25843 raw25843Labels = mixedMoment B raw25843step0 raw25843step0Labels := by
      have hz : ∀ j, raw25843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25843step0 = (fun i j => raw25843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25843step0 raw25843; decide +kernel
      have hl : raw25843step0Labels = raw25843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25843 raw25843Labels permutation265 hz
    mixedMoment B raw25843step0 raw25843step0Labels = mixedMoment B raw25843step1 raw25843step1Labels := by
      have ha : raw25843step1 = (fun i j => raw25843step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25843step1 raw25843step0; decide +kernel
      have hl : raw25843step1Labels = raw25843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25843step0 raw25843step0Labels permutation34 permutation6
    mixedMoment B raw25843step1 raw25843step1Labels = mixedMoment B raw25843step2 raw25843step2Labels := by
      have ha : raw25843step2 = raw25843step1 := by apply Matrix.ext; unfold raw25843step2 raw25843step1; decide +kernel
      have hl : raw25843step1Labels = labelEmbedding9 ∘ raw25843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25843step1 raw25843step1Labels raw25843step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw25844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw25844step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25844 raw25844Labels = mixedMoment B node4492 node4492Labels := by
  calc
    mixedMoment B raw25844 raw25844Labels = mixedMoment B raw25844step0 raw25844step0Labels := by
      have hz : ∀ j, raw25844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25844step0 = (fun i j => raw25844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25844step0 raw25844; decide +kernel
      have hl : raw25844step0Labels = raw25844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25844 raw25844Labels permutation346 hz
    mixedMoment B raw25844step0 raw25844step0Labels = mixedMoment B raw25844step1 raw25844step1Labels := by
      have hz : ∀ j, raw25844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25844step1 = (fun i j => raw25844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25844step1 raw25844step0; decide +kernel
      have hl : raw25844step1Labels = raw25844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25844step0 raw25844step0Labels permutation56 hz
    mixedMoment B raw25844step1 raw25844step1Labels = mixedMoment B raw25844step2 raw25844step2Labels := by
      have ha : raw25844step2 = (fun i j => raw25844step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25844step2 raw25844step1; decide +kernel
      have hl : raw25844step2Labels = raw25844step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25844step1 raw25844step1Labels permutation10 permutation6
    mixedMoment B raw25844step2 raw25844step2Labels = mixedMoment B raw25844step3 raw25844step3Labels := by
      have ha : raw25844step3 = raw25844step2 := by apply Matrix.ext; unfold raw25844step3 raw25844step2; decide +kernel
      have hl : raw25844step2Labels = labelEmbedding9 ∘ raw25844step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25844step2 raw25844step2Labels raw25844step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4492 node4492Labels := by rfl

def raw25845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25845step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw25845step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25845step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25845step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25845 raw25845Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw25845 raw25845Labels = mixedMoment B raw25845step0 raw25845step0Labels := by
      have hz : ∀ j, raw25845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25845step0 = (fun i j => raw25845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25845step0 raw25845; decide +kernel
      have hl : raw25845step0Labels = raw25845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25845 raw25845Labels permutation346 hz
    mixedMoment B raw25845step0 raw25845step0Labels = mixedMoment B raw25845step1 raw25845step1Labels := by
      have hz : ∀ j, raw25845step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25845step1 = (fun i j => raw25845step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25845step1 raw25845step0; decide +kernel
      have hl : raw25845step1Labels = raw25845step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25845step0 raw25845step0Labels permutation56 hz
    mixedMoment B raw25845step1 raw25845step1Labels = mixedMoment B raw25845step2 raw25845step2Labels := by
      have ha : raw25845step2 = (fun i j => raw25845step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25845step2 raw25845step1; decide +kernel
      have hl : raw25845step2Labels = raw25845step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25845step1 raw25845step1Labels permutation10 permutation4
    mixedMoment B raw25845step2 raw25845step2Labels = mixedMoment B raw25845step3 raw25845step3Labels := by
      have ha : raw25845step3 = -raw25845step2 := by apply Matrix.ext; change ∀ i j, raw25845step3 i j = -(raw25845step2 i j); unfold raw25845step3 raw25845step2; decide +kernel
      have hl : raw25845step3Labels = raw25845step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25845step3 raw25845step3Labels = mixedMoment B raw25845step4 raw25845step4Labels := by
      have ha : raw25845step4 = raw25845step3 := by apply Matrix.ext; unfold raw25845step4 raw25845step3; decide +kernel
      have hl : raw25845step3Labels = labelEmbedding7 ∘ raw25845step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25845step3 raw25845step3Labels raw25845step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw25846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25846 raw25846Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw25846 raw25846Labels = mixedMoment B raw25846step0 raw25846step0Labels := by
      have hz : ∀ j, raw25846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25846step0 = (fun i j => raw25846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25846step0 raw25846; decide +kernel
      have hl : raw25846step0Labels = raw25846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25846 raw25846Labels permutation346 hz
    mixedMoment B raw25846step0 raw25846step0Labels = mixedMoment B raw25846step1 raw25846step1Labels := by
      have ha : raw25846step1 = (fun i j => raw25846step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25846step1 raw25846step0; decide +kernel
      have hl : raw25846step1Labels = raw25846step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25846step0 raw25846step0Labels permutation34 permutation6
    mixedMoment B raw25846step1 raw25846step1Labels = mixedMoment B raw25846step2 raw25846step2Labels := by
      have ha : raw25846step2 = raw25846step1 := by apply Matrix.ext; unfold raw25846step2 raw25846step1; decide +kernel
      have hl : raw25846step1Labels = labelEmbedding9 ∘ raw25846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25846step1 raw25846step1Labels raw25846step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw25847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25847 raw25847Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw25847 raw25847Labels = mixedMoment B raw25847step0 raw25847step0Labels := by
      have hz : ∀ j, raw25847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25847step0 = (fun i j => raw25847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25847step0 raw25847; decide +kernel
      have hl : raw25847step0Labels = raw25847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25847 raw25847Labels permutation346 hz
    mixedMoment B raw25847step0 raw25847step0Labels = mixedMoment B raw25847step1 raw25847step1Labels := by
      have hz : ∀ j, raw25847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25847step1 = (fun i j => raw25847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25847step1 raw25847step0; decide +kernel
      have hl : raw25847step1Labels = raw25847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25847step0 raw25847step0Labels permutation56 hz
    mixedMoment B raw25847step1 raw25847step1Labels = mixedMoment B raw25847step2 raw25847step2Labels := by
      have ha : raw25847step2 = (fun i j => raw25847step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25847step2 raw25847step1; decide +kernel
      have hl : raw25847step2Labels = raw25847step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25847step1 raw25847step1Labels permutation10 permutation6
    mixedMoment B raw25847step2 raw25847step2Labels = mixedMoment B raw25847step3 raw25847step3Labels := by
      have ha : raw25847step3 = raw25847step2 := by apply Matrix.ext; unfold raw25847step3 raw25847step2; decide +kernel
      have hl : raw25847step2Labels = labelEmbedding9 ∘ raw25847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25847step2 raw25847step2Labels raw25847step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw25848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25848 raw25848Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw25848 raw25848Labels = mixedMoment B raw25848step0 raw25848step0Labels := by
      have hz : ∀ j, raw25848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25848step0 = (fun i j => raw25848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25848step0 raw25848; decide +kernel
      have hl : raw25848step0Labels = raw25848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25848 raw25848Labels permutation346 hz
    mixedMoment B raw25848step0 raw25848step0Labels = mixedMoment B raw25848step1 raw25848step1Labels := by
      have hz : ∀ j, raw25848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25848step1 = (fun i j => raw25848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25848step1 raw25848step0; decide +kernel
      have hl : raw25848step1Labels = raw25848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25848step0 raw25848step0Labels permutation56 hz
    mixedMoment B raw25848step1 raw25848step1Labels = mixedMoment B raw25848step2 raw25848step2Labels := by
      have ha : raw25848step2 = (fun i j => raw25848step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25848step2 raw25848step1; decide +kernel
      have hl : raw25848step2Labels = raw25848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25848step1 raw25848step1Labels permutation10 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw25849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25849 raw25849Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw25849 raw25849Labels = mixedMoment B raw25849step0 raw25849step0Labels := by
      have hz : ∀ j, raw25849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25849step0 = (fun i j => raw25849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25849step0 raw25849; decide +kernel
      have hl : raw25849step0Labels = raw25849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25849 raw25849Labels permutation346 hz
    mixedMoment B raw25849step0 raw25849step0Labels = mixedMoment B raw25849step1 raw25849step1Labels := by
      have ha : raw25849step1 = (fun i j => raw25849step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25849step1 raw25849step0; decide +kernel
      have hl : raw25849step1Labels = raw25849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25849step0 raw25849step0Labels permutation34 permutation2
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw25850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25850 raw25850Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw25850 raw25850Labels = mixedMoment B raw25850step0 raw25850step0Labels := by
      have hz : ∀ j, raw25850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25850step0 = (fun i j => raw25850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25850step0 raw25850; decide +kernel
      have hl : raw25850step0Labels = raw25850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25850 raw25850Labels permutation265 hz
    mixedMoment B raw25850step0 raw25850step0Labels = mixedMoment B raw25850step1 raw25850step1Labels := by
      have ha : raw25850step1 = (fun i j => raw25850step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25850step1 raw25850step0; decide +kernel
      have hl : raw25850step1Labels = raw25850step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25850step0 raw25850step0Labels permutation34 permutation2
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw25851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25851 raw25851Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw25851 raw25851Labels = mixedMoment B raw25851step0 raw25851step0Labels := by
      have hz : ∀ j, raw25851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25851step0 = (fun i j => raw25851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25851step0 raw25851; decide +kernel
      have hl : raw25851step0Labels = raw25851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25851 raw25851Labels permutation346 hz
    mixedMoment B raw25851step0 raw25851step0Labels = mixedMoment B raw25851step1 raw25851step1Labels := by
      have hz : ∀ j, raw25851step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25851step1 = (fun i j => raw25851step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25851step1 raw25851step0; decide +kernel
      have hl : raw25851step1Labels = raw25851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25851step0 raw25851step0Labels permutation56 hz
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw25852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw25852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw25852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25852 raw25852Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw25852 raw25852Labels = mixedMoment B raw25852step0 raw25852step0Labels := by
      have hz : ∀ j, raw25852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25852step0 = (fun i j => raw25852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25852step0 raw25852; decide +kernel
      have hl : raw25852step0Labels = raw25852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25852 raw25852Labels permutation346 hz
    mixedMoment B raw25852step0 raw25852step0Labels = mixedMoment B raw25852step1 raw25852step1Labels := by
      have hz : ∀ j, raw25852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25852step1 = (fun i j => raw25852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25852step1 raw25852step0; decide +kernel
      have hl : raw25852step1Labels = raw25852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25852step0 raw25852step0Labels permutation56 hz
    mixedMoment B raw25852step1 raw25852step1Labels = mixedMoment B raw25852step2 raw25852step2Labels := by
      have ha : raw25852step2 = (fun i j => raw25852step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25852step2 raw25852step1; decide +kernel
      have hl : raw25852step2Labels = raw25852step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25852step1 raw25852step1Labels permutation10 permutation2
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw25853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw25853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25853 raw25853Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw25853 raw25853Labels = mixedMoment B raw25853step0 raw25853step0Labels := by
      have hz : ∀ j, raw25853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25853step0 = (fun i j => raw25853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25853step0 raw25853; decide +kernel
      have hl : raw25853step0Labels = raw25853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25853 raw25853Labels permutation346 hz
    mixedMoment B raw25853step0 raw25853step0Labels = mixedMoment B raw25853step1 raw25853step1Labels := by
      have hz : ∀ j, raw25853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25853step1 = (fun i j => raw25853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25853step1 raw25853step0; decide +kernel
      have hl : raw25853step1Labels = raw25853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25853step0 raw25853step0Labels permutation56 hz
    mixedMoment B raw25853step1 raw25853step1Labels = mixedMoment B raw25853step2 raw25853step2Labels := by
      have ha : raw25853step2 = (fun i j => raw25853step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25853step2 raw25853step1; decide +kernel
      have hl : raw25853step2Labels = raw25853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25853step1 raw25853step1Labels permutation10 permutation2
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw25854 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw25854step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25854step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw25854step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25854 raw25854Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw25854 raw25854Labels = mixedMoment B raw25854step0 raw25854step0Labels := by
      have hz : ∀ j, raw25854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25854step0 = (fun i j => raw25854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25854step0 raw25854; decide +kernel
      have hl : raw25854step0Labels = raw25854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25854 raw25854Labels permutation346 hz
    mixedMoment B raw25854step0 raw25854step0Labels = mixedMoment B raw25854step1 raw25854step1Labels := by
      have hz : ∀ j, raw25854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25854step1 = (fun i j => raw25854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25854step1 raw25854step0; decide +kernel
      have hl : raw25854step1Labels = raw25854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25854step0 raw25854step0Labels permutation56 hz
    mixedMoment B raw25854step1 raw25854step1Labels = mixedMoment B raw25854step2 raw25854step2Labels := by
      have ha : raw25854step2 = (fun i j => raw25854step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25854step2 raw25854step1; decide +kernel
      have hl : raw25854step2Labels = raw25854step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25854step1 raw25854step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw25855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25855 raw25855Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw25855 raw25855Labels = mixedMoment B raw25855step0 raw25855step0Labels := by
      have hz : ∀ j, raw25855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25855step0 = (fun i j => raw25855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25855step0 raw25855; decide +kernel
      have hl : raw25855step0Labels = raw25855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25855 raw25855Labels permutation346 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
