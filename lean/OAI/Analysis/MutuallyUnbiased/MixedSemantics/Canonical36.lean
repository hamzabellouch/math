import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4608step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4608 raw4608Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw4608 raw4608Labels = mixedMoment B raw4608step0 raw4608step0Labels := by
      have hz : ∀ j, raw4608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4608step0 = (fun i j => raw4608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4608step0 raw4608; decide +kernel
      have hl : raw4608step0Labels = raw4608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4608 raw4608Labels permutation346 hz
    mixedMoment B raw4608step0 raw4608step0Labels = mixedMoment B raw4608step1 raw4608step1Labels := by
      have ha : raw4608step1 = (fun i j => raw4608step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4608step1 raw4608step0; decide +kernel
      have hl : raw4608step1Labels = raw4608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4608step0 raw4608step0Labels permutation137 permutation3
    mixedMoment B raw4608step1 raw4608step1Labels = mixedMoment B raw4608step2 raw4608step2Labels := by
      have ha : raw4608step2 = -raw4608step1 := by apply Matrix.ext; change ∀ i j, raw4608step2 i j = -(raw4608step1 i j); unfold raw4608step2 raw4608step1; decide +kernel
      have hl : raw4608step2Labels = raw4608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4608step2 raw4608step2Labels = mixedMoment B raw4608step3 raw4608step3Labels := by
      have ha : raw4608step3 = raw4608step2 := by apply Matrix.ext; unfold raw4608step3 raw4608step2; decide +kernel
      have hl : raw4608step2Labels = labelEmbedding6 ∘ raw4608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4608step2 raw4608step2Labels raw4608step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw4609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4609 raw4609Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw4609 raw4609Labels = mixedMoment B raw4609step0 raw4609step0Labels := by
      have hz : ∀ j, raw4609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4609step0 = (fun i j => raw4609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4609step0 raw4609; decide +kernel
      have hl : raw4609step0Labels = raw4609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4609 raw4609Labels permutation265 hz
    mixedMoment B raw4609step0 raw4609step0Labels = mixedMoment B raw4609step1 raw4609step1Labels := by
      have ha : raw4609step1 = (fun i j => raw4609step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4609step1 raw4609step0; decide +kernel
      have hl : raw4609step1Labels = raw4609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4609step0 raw4609step0Labels permutation40 permutation3
    mixedMoment B raw4609step1 raw4609step1Labels = mixedMoment B raw4609step2 raw4609step2Labels := by
      have ha : raw4609step2 = raw4609step1 := by apply Matrix.ext; unfold raw4609step2 raw4609step1; decide +kernel
      have hl : raw4609step1Labels = labelEmbedding6 ∘ raw4609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4609step1 raw4609step1Labels raw4609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw4610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4610step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4610 raw4610Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw4610 raw4610Labels = mixedMoment B raw4610step0 raw4610step0Labels := by
      have ha : raw4610step0 = (fun i j => raw4610 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4610step0 raw4610; decide +kernel
      have hl : raw4610step0Labels = raw4610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4610 raw4610Labels permutation640 permutation3
    mixedMoment B raw4610step0 raw4610step0Labels = mixedMoment B raw4610step1 raw4610step1Labels := by
      have ha : raw4610step1 = -raw4610step0 := by apply Matrix.ext; change ∀ i j, raw4610step1 i j = -(raw4610step0 i j); unfold raw4610step1 raw4610step0; decide +kernel
      have hl : raw4610step1Labels = raw4610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4610step1 raw4610step1Labels = mixedMoment B raw4610step2 raw4610step2Labels := by
      have ha : raw4610step2 = raw4610step1 := by apply Matrix.ext; unfold raw4610step2 raw4610step1; decide +kernel
      have hl : raw4610step1Labels = labelEmbedding6 ∘ raw4610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4610step1 raw4610step1Labels raw4610step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw4611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4611 raw4611Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw4611 raw4611Labels = mixedMoment B raw4611step0 raw4611step0Labels := by
      have hz : ∀ j, raw4611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4611step0 = (fun i j => raw4611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4611step0 raw4611; decide +kernel
      have hl : raw4611step0Labels = raw4611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4611 raw4611Labels permutation265 hz
    mixedMoment B raw4611step0 raw4611step0Labels = mixedMoment B raw4611step1 raw4611step1Labels := by
      have ha : raw4611step1 = (fun i j => raw4611step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4611step1 raw4611step0; decide +kernel
      have hl : raw4611step1Labels = raw4611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4611step0 raw4611step0Labels permutation139 permutation3
    mixedMoment B raw4611step1 raw4611step1Labels = mixedMoment B raw4611step2 raw4611step2Labels := by
      have ha : raw4611step2 = -raw4611step1 := by apply Matrix.ext; change ∀ i j, raw4611step2 i j = -(raw4611step1 i j); unfold raw4611step2 raw4611step1; decide +kernel
      have hl : raw4611step2Labels = raw4611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4611step2 raw4611step2Labels = mixedMoment B raw4611step3 raw4611step3Labels := by
      have ha : raw4611step3 = raw4611step2 := by apply Matrix.ext; unfold raw4611step3 raw4611step2; decide +kernel
      have hl : raw4611step2Labels = labelEmbedding6 ∘ raw4611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4611step2 raw4611step2Labels raw4611step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw4612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4612 raw4612Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw4612 raw4612Labels = mixedMoment B raw4612step0 raw4612step0Labels := by
      have hz : ∀ j, raw4612 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4612step0 = (fun i j => raw4612 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4612step0 raw4612; decide +kernel
      have hl : raw4612step0Labels = raw4612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4612 raw4612Labels permutation265 hz
    mixedMoment B raw4612step0 raw4612step0Labels = mixedMoment B raw4612step1 raw4612step1Labels := by
      have ha : raw4612step1 = (fun i j => raw4612step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4612step1 raw4612step0; decide +kernel
      have hl : raw4612step1Labels = raw4612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4612step0 raw4612step0Labels permutation137 permutation3
    mixedMoment B raw4612step1 raw4612step1Labels = mixedMoment B raw4612step2 raw4612step2Labels := by
      have ha : raw4612step2 = -raw4612step1 := by apply Matrix.ext; change ∀ i j, raw4612step2 i j = -(raw4612step1 i j); unfold raw4612step2 raw4612step1; decide +kernel
      have hl : raw4612step2Labels = raw4612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4612step2 raw4612step2Labels = mixedMoment B raw4612step3 raw4612step3Labels := by
      have ha : raw4612step3 = raw4612step2 := by apply Matrix.ext; unfold raw4612step3 raw4612step2; decide +kernel
      have hl : raw4612step2Labels = labelEmbedding6 ∘ raw4612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4612step2 raw4612step2Labels raw4612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw4613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4613step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4613step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4613 raw4613Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw4613 raw4613Labels = mixedMoment B raw4613step0 raw4613step0Labels := by
      have hz : ∀ j, raw4613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4613step0 = (fun i j => raw4613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4613step0 raw4613; decide +kernel
      have hl : raw4613step0Labels = raw4613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4613 raw4613Labels permutation346 hz
    mixedMoment B raw4613step0 raw4613step0Labels = mixedMoment B raw4613step1 raw4613step1Labels := by
      have hz : ∀ j, raw4613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4613step1 = (fun i j => raw4613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4613step1 raw4613step0; decide +kernel
      have hl : raw4613step1Labels = raw4613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4613step0 raw4613step0Labels permutation56 hz
    mixedMoment B raw4613step1 raw4613step1Labels = mixedMoment B raw4613step2 raw4613step2Labels := by
      have ha : raw4613step2 = (fun i j => raw4613step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4613step2 raw4613step1; decide +kernel
      have hl : raw4613step2Labels = raw4613step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4613step1 raw4613step1Labels permutation10 permutation3
    mixedMoment B raw4613step2 raw4613step2Labels = mixedMoment B raw4613step3 raw4613step3Labels := by
      have ha : raw4613step3 = raw4613step2 := by apply Matrix.ext; unfold raw4613step3 raw4613step2; decide +kernel
      have hl : raw4613step2Labels = labelEmbedding6 ∘ raw4613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4613step2 raw4613step2Labels raw4613step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw4614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4614step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4614step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4614 raw4614Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4614 raw4614Labels = mixedMoment B raw4614step0 raw4614step0Labels := by
      have hz : ∀ j, raw4614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4614step0 = (fun i j => raw4614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4614step0 raw4614; decide +kernel
      have hl : raw4614step0Labels = raw4614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4614 raw4614Labels permutation346 hz
    mixedMoment B raw4614step0 raw4614step0Labels = mixedMoment B raw4614step1 raw4614step1Labels := by
      have ha : raw4614step1 = (fun i j => raw4614step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4614step1 raw4614step0; decide +kernel
      have hl : raw4614step1Labels = raw4614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4614step0 raw4614step0Labels permutation145 permutation3
    mixedMoment B raw4614step1 raw4614step1Labels = mixedMoment B raw4614step2 raw4614step2Labels := by
      have ha : raw4614step2 = -raw4614step1 := by apply Matrix.ext; change ∀ i j, raw4614step2 i j = -(raw4614step1 i j); unfold raw4614step2 raw4614step1; decide +kernel
      have hl : raw4614step2Labels = raw4614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4614step2 raw4614step2Labels = mixedMoment B raw4614step3 raw4614step3Labels := by
      have ha : raw4614step3 = raw4614step2 := by apply Matrix.ext; unfold raw4614step3 raw4614step2; decide +kernel
      have hl : raw4614step2Labels = labelEmbedding6 ∘ raw4614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4614step2 raw4614step2Labels raw4614step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4615step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4615step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4615 raw4615Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4615 raw4615Labels = mixedMoment B raw4615step0 raw4615step0Labels := by
      have hz : ∀ j, raw4615 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4615step0 = (fun i j => raw4615 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4615step0 raw4615; decide +kernel
      have hl : raw4615step0Labels = raw4615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4615 raw4615Labels permutation265 hz
    mixedMoment B raw4615step0 raw4615step0Labels = mixedMoment B raw4615step1 raw4615step1Labels := by
      have ha : raw4615step1 = (fun i j => raw4615step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4615step1 raw4615step0; decide +kernel
      have hl : raw4615step1Labels = raw4615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4615step0 raw4615step0Labels permutation145 permutation3
    mixedMoment B raw4615step1 raw4615step1Labels = mixedMoment B raw4615step2 raw4615step2Labels := by
      have ha : raw4615step2 = -raw4615step1 := by apply Matrix.ext; change ∀ i j, raw4615step2 i j = -(raw4615step1 i j); unfold raw4615step2 raw4615step1; decide +kernel
      have hl : raw4615step2Labels = raw4615step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4615step2 raw4615step2Labels = mixedMoment B raw4615step3 raw4615step3Labels := by
      have ha : raw4615step3 = raw4615step2 := by apply Matrix.ext; unfold raw4615step3 raw4615step2; decide +kernel
      have hl : raw4615step2Labels = labelEmbedding6 ∘ raw4615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4615step2 raw4615step2Labels raw4615step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4616step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4616step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4616step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4616step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4616 raw4616Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4616 raw4616Labels = mixedMoment B raw4616step0 raw4616step0Labels := by
      have hz : ∀ j, raw4616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4616step0 = (fun i j => raw4616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4616step0 raw4616; decide +kernel
      have hl : raw4616step0Labels = raw4616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4616 raw4616Labels permutation346 hz
    mixedMoment B raw4616step0 raw4616step0Labels = mixedMoment B raw4616step1 raw4616step1Labels := by
      have hz : ∀ j, raw4616step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4616step1 = (fun i j => raw4616step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4616step1 raw4616step0; decide +kernel
      have hl : raw4616step1Labels = raw4616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4616step0 raw4616step0Labels permutation56 hz
    mixedMoment B raw4616step1 raw4616step1Labels = mixedMoment B raw4616step2 raw4616step2Labels := by
      have ha : raw4616step2 = (fun i j => raw4616step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4616step2 raw4616step1; decide +kernel
      have hl : raw4616step2Labels = raw4616step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4616step1 raw4616step1Labels permutation29 permutation3
    mixedMoment B raw4616step2 raw4616step2Labels = mixedMoment B raw4616step3 raw4616step3Labels := by
      have ha : raw4616step3 = -raw4616step2 := by apply Matrix.ext; change ∀ i j, raw4616step3 i j = -(raw4616step2 i j); unfold raw4616step3 raw4616step2; decide +kernel
      have hl : raw4616step3Labels = raw4616step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4616step3 raw4616step3Labels = mixedMoment B raw4616step4 raw4616step4Labels := by
      have ha : raw4616step4 = raw4616step3 := by apply Matrix.ext; unfold raw4616step4 raw4616step3; decide +kernel
      have hl : raw4616step3Labels = labelEmbedding6 ∘ raw4616step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4616step3 raw4616step3Labels raw4616step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw4617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4617 raw4617Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw4617 raw4617Labels = mixedMoment B raw4617step0 raw4617step0Labels := by
      have hz : ∀ j, raw4617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4617step0 = (fun i j => raw4617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4617step0 raw4617; decide +kernel
      have hl : raw4617step0Labels = raw4617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4617 raw4617Labels permutation346 hz
    mixedMoment B raw4617step0 raw4617step0Labels = mixedMoment B raw4617step1 raw4617step1Labels := by
      have hz : ∀ j, raw4617step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4617step1 = (fun i j => raw4617step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4617step1 raw4617step0; decide +kernel
      have hl : raw4617step1Labels = raw4617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4617step0 raw4617step0Labels permutation56 hz
    mixedMoment B raw4617step1 raw4617step1Labels = mixedMoment B raw4617step2 raw4617step2Labels := by
      have ha : raw4617step2 = (fun i j => raw4617step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4617step2 raw4617step1; decide +kernel
      have hl : raw4617step2Labels = raw4617step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4617step1 raw4617step1Labels permutation8 permutation3
    mixedMoment B raw4617step2 raw4617step2Labels = mixedMoment B raw4617step3 raw4617step3Labels := by
      have ha : raw4617step3 = raw4617step2 := by apply Matrix.ext; unfold raw4617step3 raw4617step2; decide +kernel
      have hl : raw4617step2Labels = labelEmbedding6 ∘ raw4617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4617step2 raw4617step2Labels raw4617step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw4618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4618 raw4618Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4618 raw4618Labels = mixedMoment B raw4618step0 raw4618step0Labels := by
      have hz : ∀ j, raw4618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4618step0 = (fun i j => raw4618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4618step0 raw4618; decide +kernel
      have hl : raw4618step0Labels = raw4618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4618 raw4618Labels permutation346 hz
    mixedMoment B raw4618step0 raw4618step0Labels = mixedMoment B raw4618step1 raw4618step1Labels := by
      have ha : raw4618step1 = (fun i j => raw4618step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4618step1 raw4618step0; decide +kernel
      have hl : raw4618step1Labels = raw4618step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4618step0 raw4618step0Labels permutation151 permutation3
    mixedMoment B raw4618step1 raw4618step1Labels = mixedMoment B raw4618step2 raw4618step2Labels := by
      have ha : raw4618step2 = -raw4618step1 := by apply Matrix.ext; change ∀ i j, raw4618step2 i j = -(raw4618step1 i j); unfold raw4618step2 raw4618step1; decide +kernel
      have hl : raw4618step2Labels = raw4618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4618step2 raw4618step2Labels = mixedMoment B raw4618step3 raw4618step3Labels := by
      have ha : raw4618step3 = raw4618step2 := by apply Matrix.ext; unfold raw4618step3 raw4618step2; decide +kernel
      have hl : raw4618step2Labels = labelEmbedding6 ∘ raw4618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4618step2 raw4618step2Labels raw4618step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4619 raw4619Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4619 raw4619Labels = mixedMoment B raw4619step0 raw4619step0Labels := by
      have hz : ∀ j, raw4619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4619step0 = (fun i j => raw4619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4619step0 raw4619; decide +kernel
      have hl : raw4619step0Labels = raw4619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4619 raw4619Labels permutation265 hz
    mixedMoment B raw4619step0 raw4619step0Labels = mixedMoment B raw4619step1 raw4619step1Labels := by
      have ha : raw4619step1 = (fun i j => raw4619step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4619step1 raw4619step0; decide +kernel
      have hl : raw4619step1Labels = raw4619step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4619step0 raw4619step0Labels permutation151 permutation3
    mixedMoment B raw4619step1 raw4619step1Labels = mixedMoment B raw4619step2 raw4619step2Labels := by
      have ha : raw4619step2 = -raw4619step1 := by apply Matrix.ext; change ∀ i j, raw4619step2 i j = -(raw4619step1 i j); unfold raw4619step2 raw4619step1; decide +kernel
      have hl : raw4619step2Labels = raw4619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4619step2 raw4619step2Labels = mixedMoment B raw4619step3 raw4619step3Labels := by
      have ha : raw4619step3 = raw4619step2 := by apply Matrix.ext; unfold raw4619step3 raw4619step2; decide +kernel
      have hl : raw4619step2Labels = labelEmbedding6 ∘ raw4619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4619step2 raw4619step2Labels raw4619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4620 raw4620Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw4620 raw4620Labels = mixedMoment B raw4620step0 raw4620step0Labels := by
      have hz : ∀ j, raw4620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4620step0 = (fun i j => raw4620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4620step0 raw4620; decide +kernel
      have hl : raw4620step0Labels = raw4620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4620 raw4620Labels permutation346 hz
    mixedMoment B raw4620step0 raw4620step0Labels = mixedMoment B raw4620step1 raw4620step1Labels := by
      have hz : ∀ j, raw4620step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4620step1 = (fun i j => raw4620step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4620step1 raw4620step0; decide +kernel
      have hl : raw4620step1Labels = raw4620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4620step0 raw4620step0Labels permutation56 hz
    mixedMoment B raw4620step1 raw4620step1Labels = mixedMoment B raw4620step2 raw4620step2Labels := by
      have ha : raw4620step2 = (fun i j => raw4620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4620step2 raw4620step1; decide +kernel
      have hl : raw4620step2Labels = raw4620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4620step1 raw4620step1Labels permutation31 permutation3
    mixedMoment B raw4620step2 raw4620step2Labels = mixedMoment B raw4620step3 raw4620step3Labels := by
      have ha : raw4620step3 = -raw4620step2 := by apply Matrix.ext; change ∀ i j, raw4620step3 i j = -(raw4620step2 i j); unfold raw4620step3 raw4620step2; decide +kernel
      have hl : raw4620step3Labels = raw4620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4620step3 raw4620step3Labels = mixedMoment B raw4620step4 raw4620step4Labels := by
      have ha : raw4620step4 = raw4620step3 := by apply Matrix.ext; unfold raw4620step4 raw4620step3; decide +kernel
      have hl : raw4620step3Labels = labelEmbedding6 ∘ raw4620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4620step3 raw4620step3Labels raw4620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw4621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4621step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4621step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4621step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4621 raw4621Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw4621 raw4621Labels = mixedMoment B raw4621step0 raw4621step0Labels := by
      have hz : ∀ j, raw4621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4621step0 = (fun i j => raw4621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4621step0 raw4621; decide +kernel
      have hl : raw4621step0Labels = raw4621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4621 raw4621Labels permutation346 hz
    mixedMoment B raw4621step0 raw4621step0Labels = mixedMoment B raw4621step1 raw4621step1Labels := by
      have hz : ∀ j, raw4621step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4621step1 = (fun i j => raw4621step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4621step1 raw4621step0; decide +kernel
      have hl : raw4621step1Labels = raw4621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4621step0 raw4621step0Labels permutation56 hz
    mixedMoment B raw4621step1 raw4621step1Labels = mixedMoment B raw4621step2 raw4621step2Labels := by
      have ha : raw4621step2 = (fun i j => raw4621step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4621step2 raw4621step1; decide +kernel
      have hl : raw4621step2Labels = raw4621step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4621step1 raw4621step1Labels permutation29 permutation3
    mixedMoment B raw4621step2 raw4621step2Labels = mixedMoment B raw4621step3 raw4621step3Labels := by
      have ha : raw4621step3 = -raw4621step2 := by apply Matrix.ext; change ∀ i j, raw4621step3 i j = -(raw4621step2 i j); unfold raw4621step3 raw4621step2; decide +kernel
      have hl : raw4621step3Labels = raw4621step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4621step3 raw4621step3Labels = mixedMoment B raw4621step4 raw4621step4Labels := by
      have ha : raw4621step4 = raw4621step3 := by apply Matrix.ext; unfold raw4621step4 raw4621step3; decide +kernel
      have hl : raw4621step3Labels = labelEmbedding6 ∘ raw4621step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4621step3 raw4621step3Labels raw4621step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw4622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4622 raw4622Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw4622 raw4622Labels = mixedMoment B raw4622step0 raw4622step0Labels := by
      have hz : ∀ j, raw4622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4622step0 = (fun i j => raw4622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4622step0 raw4622; decide +kernel
      have hl : raw4622step0Labels = raw4622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4622 raw4622Labels permutation346 hz
    mixedMoment B raw4622step0 raw4622step0Labels = mixedMoment B raw4622step1 raw4622step1Labels := by
      have ha : raw4622step1 = (fun i j => raw4622step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4622step1 raw4622step0; decide +kernel
      have hl : raw4622step1Labels = raw4622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4622step0 raw4622step0Labels permutation145 permutation3
    mixedMoment B raw4622step1 raw4622step1Labels = mixedMoment B raw4622step2 raw4622step2Labels := by
      have ha : raw4622step2 = -raw4622step1 := by apply Matrix.ext; change ∀ i j, raw4622step2 i j = -(raw4622step1 i j); unfold raw4622step2 raw4622step1; decide +kernel
      have hl : raw4622step2Labels = raw4622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4622step2 raw4622step2Labels = mixedMoment B raw4622step3 raw4622step3Labels := by
      have ha : raw4622step3 = raw4622step2 := by apply Matrix.ext; unfold raw4622step3 raw4622step2; decide +kernel
      have hl : raw4622step2Labels = labelEmbedding6 ∘ raw4622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4622step2 raw4622step2Labels raw4622step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw4623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4623step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4623step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4623 raw4623Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw4623 raw4623Labels = mixedMoment B raw4623step0 raw4623step0Labels := by
      have hz : ∀ j, raw4623 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4623step0 = (fun i j => raw4623 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4623step0 raw4623; decide +kernel
      have hl : raw4623step0Labels = raw4623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4623 raw4623Labels permutation265 hz
    mixedMoment B raw4623step0 raw4623step0Labels = mixedMoment B raw4623step1 raw4623step1Labels := by
      have ha : raw4623step1 = (fun i j => raw4623step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4623step1 raw4623step0; decide +kernel
      have hl : raw4623step1Labels = raw4623step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4623step0 raw4623step0Labels permutation145 permutation3
    mixedMoment B raw4623step1 raw4623step1Labels = mixedMoment B raw4623step2 raw4623step2Labels := by
      have ha : raw4623step2 = -raw4623step1 := by apply Matrix.ext; change ∀ i j, raw4623step2 i j = -(raw4623step1 i j); unfold raw4623step2 raw4623step1; decide +kernel
      have hl : raw4623step2Labels = raw4623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4623step2 raw4623step2Labels = mixedMoment B raw4623step3 raw4623step3Labels := by
      have ha : raw4623step3 = raw4623step2 := by apply Matrix.ext; unfold raw4623step3 raw4623step2; decide +kernel
      have hl : raw4623step2Labels = labelEmbedding6 ∘ raw4623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4623step2 raw4623step2Labels raw4623step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw4624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4624step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4624step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4624step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4624step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4624 raw4624Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw4624 raw4624Labels = mixedMoment B raw4624step0 raw4624step0Labels := by
      have hz : ∀ j, raw4624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4624step0 = (fun i j => raw4624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4624step0 raw4624; decide +kernel
      have hl : raw4624step0Labels = raw4624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4624 raw4624Labels permutation346 hz
    mixedMoment B raw4624step0 raw4624step0Labels = mixedMoment B raw4624step1 raw4624step1Labels := by
      have hz : ∀ j, raw4624step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4624step1 = (fun i j => raw4624step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4624step1 raw4624step0; decide +kernel
      have hl : raw4624step1Labels = raw4624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4624step0 raw4624step0Labels permutation56 hz
    mixedMoment B raw4624step1 raw4624step1Labels = mixedMoment B raw4624step2 raw4624step2Labels := by
      have ha : raw4624step2 = (fun i j => raw4624step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4624step2 raw4624step1; decide +kernel
      have hl : raw4624step2Labels = raw4624step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4624step1 raw4624step1Labels permutation31 permutation3
    mixedMoment B raw4624step2 raw4624step2Labels = mixedMoment B raw4624step3 raw4624step3Labels := by
      have ha : raw4624step3 = -raw4624step2 := by apply Matrix.ext; change ∀ i j, raw4624step3 i j = -(raw4624step2 i j); unfold raw4624step3 raw4624step2; decide +kernel
      have hl : raw4624step3Labels = raw4624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4624step3 raw4624step3Labels = mixedMoment B raw4624step4 raw4624step4Labels := by
      have ha : raw4624step4 = raw4624step3 := by apply Matrix.ext; unfold raw4624step4 raw4624step3; decide +kernel
      have hl : raw4624step3Labels = labelEmbedding6 ∘ raw4624step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4624step3 raw4624step3Labels raw4624step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw4625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4625step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4625step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4625step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4625step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4625 raw4625Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw4625 raw4625Labels = mixedMoment B raw4625step0 raw4625step0Labels := by
      have hz : ∀ j, raw4625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4625step0 = (fun i j => raw4625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4625step0 raw4625; decide +kernel
      have hl : raw4625step0Labels = raw4625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4625 raw4625Labels permutation346 hz
    mixedMoment B raw4625step0 raw4625step0Labels = mixedMoment B raw4625step1 raw4625step1Labels := by
      have hz : ∀ j, raw4625step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4625step1 = (fun i j => raw4625step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4625step1 raw4625step0; decide +kernel
      have hl : raw4625step1Labels = raw4625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4625step0 raw4625step0Labels permutation56 hz
    mixedMoment B raw4625step1 raw4625step1Labels = mixedMoment B raw4625step2 raw4625step2Labels := by
      have ha : raw4625step2 = (fun i j => raw4625step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4625step2 raw4625step1; decide +kernel
      have hl : raw4625step2Labels = raw4625step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4625step1 raw4625step1Labels permutation29 permutation3
    mixedMoment B raw4625step2 raw4625step2Labels = mixedMoment B raw4625step3 raw4625step3Labels := by
      have ha : raw4625step3 = -raw4625step2 := by apply Matrix.ext; change ∀ i j, raw4625step3 i j = -(raw4625step2 i j); unfold raw4625step3 raw4625step2; decide +kernel
      have hl : raw4625step3Labels = raw4625step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4625step3 raw4625step3Labels = mixedMoment B raw4625step4 raw4625step4Labels := by
      have ha : raw4625step4 = raw4625step3 := by apply Matrix.ext; unfold raw4625step4 raw4625step3; decide +kernel
      have hl : raw4625step3Labels = labelEmbedding6 ∘ raw4625step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4625step3 raw4625step3Labels raw4625step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw4626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw4626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4626 raw4626Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw4626 raw4626Labels = mixedMoment B raw4626step0 raw4626step0Labels := by
      have hz : ∀ j, raw4626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4626step0 = (fun i j => raw4626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4626step0 raw4626; decide +kernel
      have hl : raw4626step0Labels = raw4626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4626 raw4626Labels permutation346 hz
    mixedMoment B raw4626step0 raw4626step0Labels = mixedMoment B raw4626step1 raw4626step1Labels := by
      have hz : ∀ j, raw4626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4626step1 = (fun i j => raw4626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4626step1 raw4626step0; decide +kernel
      have hl : raw4626step1Labels = raw4626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4626step0 raw4626step0Labels permutation56 hz
    mixedMoment B raw4626step1 raw4626step1Labels = mixedMoment B raw4626step2 raw4626step2Labels := by
      have ha : raw4626step2 = (fun i j => raw4626step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4626step2 raw4626step1; decide +kernel
      have hl : raw4626step2Labels = raw4626step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4626step1 raw4626step1Labels permutation29 permutation3
    mixedMoment B raw4626step2 raw4626step2Labels = mixedMoment B raw4626step3 raw4626step3Labels := by
      have ha : raw4626step3 = -raw4626step2 := by apply Matrix.ext; change ∀ i j, raw4626step3 i j = -(raw4626step2 i j); unfold raw4626step3 raw4626step2; decide +kernel
      have hl : raw4626step3Labels = raw4626step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw4627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4627 raw4627Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw4627 raw4627Labels = mixedMoment B raw4627step0 raw4627step0Labels := by
      have hz : ∀ j, raw4627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4627step0 = (fun i j => raw4627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4627step0 raw4627; decide +kernel
      have hl : raw4627step0Labels = raw4627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4627 raw4627Labels permutation346 hz
    mixedMoment B raw4627step0 raw4627step0Labels = mixedMoment B raw4627step1 raw4627step1Labels := by
      have ha : raw4627step1 = (fun i j => raw4627step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4627step1 raw4627step0; decide +kernel
      have hl : raw4627step1Labels = raw4627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4627step0 raw4627step0Labels permutation40 permutation3
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw4628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4628 raw4628Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw4628 raw4628Labels = mixedMoment B raw4628step0 raw4628step0Labels := by
      have ha : raw4628step0 = (fun i j => raw4628 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4628step0 raw4628; decide +kernel
      have hl : raw4628step0Labels = raw4628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4628 raw4628Labels permutation616 permutation3
    mixedMoment B raw4628step0 raw4628step0Labels = mixedMoment B raw4628step1 raw4628step1Labels := by
      have ha : raw4628step1 = -raw4628step0 := by apply Matrix.ext; change ∀ i j, raw4628step1 i j = -(raw4628step0 i j); unfold raw4628step1 raw4628step0; decide +kernel
      have hl : raw4628step1Labels = raw4628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw4629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4629 raw4629Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw4629 raw4629Labels = mixedMoment B raw4629step0 raw4629step0Labels := by
      have hz : ∀ j, raw4629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4629step0 = (fun i j => raw4629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4629step0 raw4629; decide +kernel
      have hl : raw4629step0Labels = raw4629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4629 raw4629Labels permutation346 hz
    mixedMoment B raw4629step0 raw4629step0Labels = mixedMoment B raw4629step1 raw4629step1Labels := by
      have ha : raw4629step1 = (fun i j => raw4629step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4629step1 raw4629step0; decide +kernel
      have hl : raw4629step1Labels = raw4629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4629step0 raw4629step0Labels permutation139 permutation3
    mixedMoment B raw4629step1 raw4629step1Labels = mixedMoment B raw4629step2 raw4629step2Labels := by
      have ha : raw4629step2 = -raw4629step1 := by apply Matrix.ext; change ∀ i j, raw4629step2 i j = -(raw4629step1 i j); unfold raw4629step2 raw4629step1; decide +kernel
      have hl : raw4629step2Labels = raw4629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw4630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4630 raw4630Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw4630 raw4630Labels = mixedMoment B raw4630step0 raw4630step0Labels := by
      have hz : ∀ j, raw4630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4630step0 = (fun i j => raw4630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4630step0 raw4630; decide +kernel
      have hl : raw4630step0Labels = raw4630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4630 raw4630Labels permutation346 hz
    mixedMoment B raw4630step0 raw4630step0Labels = mixedMoment B raw4630step1 raw4630step1Labels := by
      have ha : raw4630step1 = (fun i j => raw4630step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4630step1 raw4630step0; decide +kernel
      have hl : raw4630step1Labels = raw4630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4630step0 raw4630step0Labels permutation137 permutation3
    mixedMoment B raw4630step1 raw4630step1Labels = mixedMoment B raw4630step2 raw4630step2Labels := by
      have ha : raw4630step2 = -raw4630step1 := by apply Matrix.ext; change ∀ i j, raw4630step2 i j = -(raw4630step1 i j); unfold raw4630step2 raw4630step1; decide +kernel
      have hl : raw4630step2Labels = raw4630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw4631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw4631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4631 raw4631Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw4631 raw4631Labels = mixedMoment B raw4631step0 raw4631step0Labels := by
      have hz : ∀ j, raw4631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4631step0 = (fun i j => raw4631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4631step0 raw4631; decide +kernel
      have hl : raw4631step0Labels = raw4631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4631 raw4631Labels permutation265 hz
    mixedMoment B raw4631step0 raw4631step0Labels = mixedMoment B raw4631step1 raw4631step1Labels := by
      have ha : raw4631step1 = (fun i j => raw4631step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4631step1 raw4631step0; decide +kernel
      have hl : raw4631step1Labels = raw4631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4631step0 raw4631step0Labels permutation40 permutation3
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw4632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4632 raw4632Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw4632 raw4632Labels = mixedMoment B raw4632step0 raw4632step0Labels := by
      have ha : raw4632step0 = (fun i j => raw4632 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4632step0 raw4632; decide +kernel
      have hl : raw4632step0Labels = raw4632Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4632 raw4632Labels permutation640 permutation3
    mixedMoment B raw4632step0 raw4632step0Labels = mixedMoment B raw4632step1 raw4632step1Labels := by
      have ha : raw4632step1 = -raw4632step0 := by apply Matrix.ext; change ∀ i j, raw4632step1 i j = -(raw4632step0 i j); unfold raw4632step1 raw4632step0; decide +kernel
      have hl : raw4632step1Labels = raw4632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw4633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4633 raw4633Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw4633 raw4633Labels = mixedMoment B raw4633step0 raw4633step0Labels := by
      have hz : ∀ j, raw4633 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4633step0 = (fun i j => raw4633 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4633step0 raw4633; decide +kernel
      have hl : raw4633step0Labels = raw4633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4633 raw4633Labels permutation265 hz
    mixedMoment B raw4633step0 raw4633step0Labels = mixedMoment B raw4633step1 raw4633step1Labels := by
      have ha : raw4633step1 = (fun i j => raw4633step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4633step1 raw4633step0; decide +kernel
      have hl : raw4633step1Labels = raw4633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4633step0 raw4633step0Labels permutation139 permutation3
    mixedMoment B raw4633step1 raw4633step1Labels = mixedMoment B raw4633step2 raw4633step2Labels := by
      have ha : raw4633step2 = -raw4633step1 := by apply Matrix.ext; change ∀ i j, raw4633step2 i j = -(raw4633step1 i j); unfold raw4633step2 raw4633step1; decide +kernel
      have hl : raw4633step2Labels = raw4633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw4634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4634 raw4634Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw4634 raw4634Labels = mixedMoment B raw4634step0 raw4634step0Labels := by
      have hz : ∀ j, raw4634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4634step0 = (fun i j => raw4634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4634step0 raw4634; decide +kernel
      have hl : raw4634step0Labels = raw4634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4634 raw4634Labels permutation265 hz
    mixedMoment B raw4634step0 raw4634step0Labels = mixedMoment B raw4634step1 raw4634step1Labels := by
      have ha : raw4634step1 = (fun i j => raw4634step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4634step1 raw4634step0; decide +kernel
      have hl : raw4634step1Labels = raw4634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4634step0 raw4634step0Labels permutation137 permutation3
    mixedMoment B raw4634step1 raw4634step1Labels = mixedMoment B raw4634step2 raw4634step2Labels := by
      have ha : raw4634step2 = -raw4634step1 := by apply Matrix.ext; change ∀ i j, raw4634step2 i j = -(raw4634step1 i j); unfold raw4634step2 raw4634step1; decide +kernel
      have hl : raw4634step2Labels = raw4634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw4635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4635 raw4635Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw4635 raw4635Labels = mixedMoment B raw4635step0 raw4635step0Labels := by
      have hz : ∀ j, raw4635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4635step0 = (fun i j => raw4635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4635step0 raw4635; decide +kernel
      have hl : raw4635step0Labels = raw4635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4635 raw4635Labels permutation346 hz
    mixedMoment B raw4635step0 raw4635step0Labels = mixedMoment B raw4635step1 raw4635step1Labels := by
      have hz : ∀ j, raw4635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4635step1 = (fun i j => raw4635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4635step1 raw4635step0; decide +kernel
      have hl : raw4635step1Labels = raw4635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4635step0 raw4635step0Labels permutation56 hz
    mixedMoment B raw4635step1 raw4635step1Labels = mixedMoment B raw4635step2 raw4635step2Labels := by
      have ha : raw4635step2 = (fun i j => raw4635step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4635step2 raw4635step1; decide +kernel
      have hl : raw4635step2Labels = raw4635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4635step1 raw4635step1Labels permutation10 permutation3
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw4636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4636 raw4636Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4636 raw4636Labels = mixedMoment B raw4636step0 raw4636step0Labels := by
      have hz : ∀ j, raw4636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4636step0 = (fun i j => raw4636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4636step0 raw4636; decide +kernel
      have hl : raw4636step0Labels = raw4636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4636 raw4636Labels permutation346 hz
    mixedMoment B raw4636step0 raw4636step0Labels = mixedMoment B raw4636step1 raw4636step1Labels := by
      have ha : raw4636step1 = (fun i j => raw4636step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4636step1 raw4636step0; decide +kernel
      have hl : raw4636step1Labels = raw4636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4636step0 raw4636step0Labels permutation145 permutation3
    mixedMoment B raw4636step1 raw4636step1Labels = mixedMoment B raw4636step2 raw4636step2Labels := by
      have ha : raw4636step2 = -raw4636step1 := by apply Matrix.ext; change ∀ i j, raw4636step2 i j = -(raw4636step1 i j); unfold raw4636step2 raw4636step1; decide +kernel
      have hl : raw4636step2Labels = raw4636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw4637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4637 raw4637Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4637 raw4637Labels = mixedMoment B raw4637step0 raw4637step0Labels := by
      have hz : ∀ j, raw4637 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4637step0 = (fun i j => raw4637 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4637step0 raw4637; decide +kernel
      have hl : raw4637step0Labels = raw4637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4637 raw4637Labels permutation265 hz
    mixedMoment B raw4637step0 raw4637step0Labels = mixedMoment B raw4637step1 raw4637step1Labels := by
      have ha : raw4637step1 = (fun i j => raw4637step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4637step1 raw4637step0; decide +kernel
      have hl : raw4637step1Labels = raw4637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4637step0 raw4637step0Labels permutation145 permutation3
    mixedMoment B raw4637step1 raw4637step1Labels = mixedMoment B raw4637step2 raw4637step2Labels := by
      have ha : raw4637step2 = -raw4637step1 := by apply Matrix.ext; change ∀ i j, raw4637step2 i j = -(raw4637step1 i j); unfold raw4637step2 raw4637step1; decide +kernel
      have hl : raw4637step2Labels = raw4637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw4638step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4638 raw4638Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4638 raw4638Labels = mixedMoment B raw4638step0 raw4638step0Labels := by
      have hz : ∀ j, raw4638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4638step0 = (fun i j => raw4638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4638step0 raw4638; decide +kernel
      have hl : raw4638step0Labels = raw4638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4638 raw4638Labels permutation346 hz
    mixedMoment B raw4638step0 raw4638step0Labels = mixedMoment B raw4638step1 raw4638step1Labels := by
      have hz : ∀ j, raw4638step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4638step1 = (fun i j => raw4638step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4638step1 raw4638step0; decide +kernel
      have hl : raw4638step1Labels = raw4638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4638step0 raw4638step0Labels permutation56 hz
    mixedMoment B raw4638step1 raw4638step1Labels = mixedMoment B raw4638step2 raw4638step2Labels := by
      have ha : raw4638step2 = (fun i j => raw4638step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4638step2 raw4638step1; decide +kernel
      have hl : raw4638step2Labels = raw4638step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4638step1 raw4638step1Labels permutation29 permutation3
    mixedMoment B raw4638step2 raw4638step2Labels = mixedMoment B raw4638step3 raw4638step3Labels := by
      have ha : raw4638step3 = -raw4638step2 := by apply Matrix.ext; change ∀ i j, raw4638step3 i j = -(raw4638step2 i j); unfold raw4638step3 raw4638step2; decide +kernel
      have hl : raw4638step3Labels = raw4638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw4639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw4639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4639 raw4639Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw4639 raw4639Labels = mixedMoment B raw4639step0 raw4639step0Labels := by
      have hz : ∀ j, raw4639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4639step0 = (fun i j => raw4639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4639step0 raw4639; decide +kernel
      have hl : raw4639step0Labels = raw4639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4639 raw4639Labels permutation346 hz
    mixedMoment B raw4639step0 raw4639step0Labels = mixedMoment B raw4639step1 raw4639step1Labels := by
      have hz : ∀ j, raw4639step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4639step1 = (fun i j => raw4639step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4639step1 raw4639step0; decide +kernel
      have hl : raw4639step1Labels = raw4639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4639step0 raw4639step0Labels permutation56 hz
    mixedMoment B raw4639step1 raw4639step1Labels = mixedMoment B raw4639step2 raw4639step2Labels := by
      have ha : raw4639step2 = (fun i j => raw4639step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4639step2 raw4639step1; decide +kernel
      have hl : raw4639step2Labels = raw4639step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4639step1 raw4639step1Labels permutation8 permutation3
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw4640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4640 raw4640Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4640 raw4640Labels = mixedMoment B raw4640step0 raw4640step0Labels := by
      have hz : ∀ j, raw4640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4640step0 = (fun i j => raw4640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4640step0 raw4640; decide +kernel
      have hl : raw4640step0Labels = raw4640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4640 raw4640Labels permutation346 hz
    mixedMoment B raw4640step0 raw4640step0Labels = mixedMoment B raw4640step1 raw4640step1Labels := by
      have ha : raw4640step1 = (fun i j => raw4640step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4640step1 raw4640step0; decide +kernel
      have hl : raw4640step1Labels = raw4640step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4640step0 raw4640step0Labels permutation151 permutation3
    mixedMoment B raw4640step1 raw4640step1Labels = mixedMoment B raw4640step2 raw4640step2Labels := by
      have ha : raw4640step2 = -raw4640step1 := by apply Matrix.ext; change ∀ i j, raw4640step2 i j = -(raw4640step1 i j); unfold raw4640step2 raw4640step1; decide +kernel
      have hl : raw4640step2Labels = raw4640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4641 raw4641Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw4641 raw4641Labels = mixedMoment B raw4641step0 raw4641step0Labels := by
      have hz : ∀ j, raw4641 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4641step0 = (fun i j => raw4641 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4641step0 raw4641; decide +kernel
      have hl : raw4641step0Labels = raw4641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4641 raw4641Labels permutation265 hz
    mixedMoment B raw4641step0 raw4641step0Labels = mixedMoment B raw4641step1 raw4641step1Labels := by
      have ha : raw4641step1 = (fun i j => raw4641step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4641step1 raw4641step0; decide +kernel
      have hl : raw4641step1Labels = raw4641step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4641step0 raw4641step0Labels permutation151 permutation3
    mixedMoment B raw4641step1 raw4641step1Labels = mixedMoment B raw4641step2 raw4641step2Labels := by
      have ha : raw4641step2 = -raw4641step1 := by apply Matrix.ext; change ∀ i j, raw4641step2 i j = -(raw4641step1 i j); unfold raw4641step2 raw4641step1; decide +kernel
      have hl : raw4641step2Labels = raw4641step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw4642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4642step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw4642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4642 raw4642Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw4642 raw4642Labels = mixedMoment B raw4642step0 raw4642step0Labels := by
      have hz : ∀ j, raw4642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4642step0 = (fun i j => raw4642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4642step0 raw4642; decide +kernel
      have hl : raw4642step0Labels = raw4642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4642 raw4642Labels permutation346 hz
    mixedMoment B raw4642step0 raw4642step0Labels = mixedMoment B raw4642step1 raw4642step1Labels := by
      have hz : ∀ j, raw4642step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4642step1 = (fun i j => raw4642step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4642step1 raw4642step0; decide +kernel
      have hl : raw4642step1Labels = raw4642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4642step0 raw4642step0Labels permutation56 hz
    mixedMoment B raw4642step1 raw4642step1Labels = mixedMoment B raw4642step2 raw4642step2Labels := by
      have ha : raw4642step2 = (fun i j => raw4642step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4642step2 raw4642step1; decide +kernel
      have hl : raw4642step2Labels = raw4642step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4642step1 raw4642step1Labels permutation31 permutation3
    mixedMoment B raw4642step2 raw4642step2Labels = mixedMoment B raw4642step3 raw4642step3Labels := by
      have ha : raw4642step3 = -raw4642step2 := by apply Matrix.ext; change ∀ i j, raw4642step3 i j = -(raw4642step2 i j); unfold raw4642step3 raw4642step2; decide +kernel
      have hl : raw4642step3Labels = raw4642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw4643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4643 raw4643Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw4643 raw4643Labels = mixedMoment B raw4643step0 raw4643step0Labels := by
      have hz : ∀ j, raw4643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4643step0 = (fun i j => raw4643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4643step0 raw4643; decide +kernel
      have hl : raw4643step0Labels = raw4643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4643 raw4643Labels permutation346 hz
    mixedMoment B raw4643step0 raw4643step0Labels = mixedMoment B raw4643step1 raw4643step1Labels := by
      have hz : ∀ j, raw4643step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4643step1 = (fun i j => raw4643step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4643step1 raw4643step0; decide +kernel
      have hl : raw4643step1Labels = raw4643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4643step0 raw4643step0Labels permutation56 hz
    mixedMoment B raw4643step1 raw4643step1Labels = mixedMoment B raw4643step2 raw4643step2Labels := by
      have ha : raw4643step2 = (fun i j => raw4643step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4643step2 raw4643step1; decide +kernel
      have hl : raw4643step2Labels = raw4643step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4643step1 raw4643step1Labels permutation29 permutation3
    mixedMoment B raw4643step2 raw4643step2Labels = mixedMoment B raw4643step3 raw4643step3Labels := by
      have ha : raw4643step3 = -raw4643step2 := by apply Matrix.ext; change ∀ i j, raw4643step3 i j = -(raw4643step2 i j); unfold raw4643step3 raw4643step2; decide +kernel
      have hl : raw4643step3Labels = raw4643step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

def raw4644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4644 raw4644Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw4644 raw4644Labels = mixedMoment B raw4644step0 raw4644step0Labels := by
      have hz : ∀ j, raw4644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4644step0 = (fun i j => raw4644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4644step0 raw4644; decide +kernel
      have hl : raw4644step0Labels = raw4644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4644 raw4644Labels permutation346 hz
    mixedMoment B raw4644step0 raw4644step0Labels = mixedMoment B raw4644step1 raw4644step1Labels := by
      have ha : raw4644step1 = (fun i j => raw4644step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4644step1 raw4644step0; decide +kernel
      have hl : raw4644step1Labels = raw4644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4644step0 raw4644step0Labels permutation145 permutation3
    mixedMoment B raw4644step1 raw4644step1Labels = mixedMoment B raw4644step2 raw4644step2Labels := by
      have ha : raw4644step2 = -raw4644step1 := by apply Matrix.ext; change ∀ i j, raw4644step2 i j = -(raw4644step1 i j); unfold raw4644step2 raw4644step1; decide +kernel
      have hl : raw4644step2Labels = raw4644step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node787 node787Labels := by rfl

def raw4645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4645 raw4645Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw4645 raw4645Labels = mixedMoment B raw4645step0 raw4645step0Labels := by
      have hz : ∀ j, raw4645 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4645step0 = (fun i j => raw4645 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4645step0 raw4645; decide +kernel
      have hl : raw4645step0Labels = raw4645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4645 raw4645Labels permutation265 hz
    mixedMoment B raw4645step0 raw4645step0Labels = mixedMoment B raw4645step1 raw4645step1Labels := by
      have ha : raw4645step1 = (fun i j => raw4645step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4645step1 raw4645step0; decide +kernel
      have hl : raw4645step1Labels = raw4645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4645step0 raw4645step0Labels permutation145 permutation3
    mixedMoment B raw4645step1 raw4645step1Labels = mixedMoment B raw4645step2 raw4645step2Labels := by
      have ha : raw4645step2 = -raw4645step1 := by apply Matrix.ext; change ∀ i j, raw4645step2 i j = -(raw4645step1 i j); unfold raw4645step2 raw4645step1; decide +kernel
      have hl : raw4645step2Labels = raw4645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node787 node787Labels := by rfl

def raw4646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![4, -4, 0]]
def raw4646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4646 raw4646Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw4646 raw4646Labels = mixedMoment B raw4646step0 raw4646step0Labels := by
      have hz : ∀ j, raw4646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4646step0 = (fun i j => raw4646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4646step0 raw4646; decide +kernel
      have hl : raw4646step0Labels = raw4646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4646 raw4646Labels permutation346 hz
    mixedMoment B raw4646step0 raw4646step0Labels = mixedMoment B raw4646step1 raw4646step1Labels := by
      have hz : ∀ j, raw4646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4646step1 = (fun i j => raw4646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4646step1 raw4646step0; decide +kernel
      have hl : raw4646step1Labels = raw4646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4646step0 raw4646step0Labels permutation56 hz
    mixedMoment B raw4646step1 raw4646step1Labels = mixedMoment B raw4646step2 raw4646step2Labels := by
      have ha : raw4646step2 = (fun i j => raw4646step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4646step2 raw4646step1; decide +kernel
      have hl : raw4646step2Labels = raw4646step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4646step1 raw4646step1Labels permutation31 permutation3
    mixedMoment B raw4646step2 raw4646step2Labels = mixedMoment B raw4646step3 raw4646step3Labels := by
      have ha : raw4646step3 = -raw4646step2 := by apply Matrix.ext; change ∀ i j, raw4646step3 i j = -(raw4646step2 i j); unfold raw4646step3 raw4646step2; decide +kernel
      have hl : raw4646step3Labels = raw4646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node813 node813Labels := by rfl

def raw4647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![4, -4, 0]]
def raw4647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4647 raw4647Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw4647 raw4647Labels = mixedMoment B raw4647step0 raw4647step0Labels := by
      have hz : ∀ j, raw4647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4647step0 = (fun i j => raw4647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4647step0 raw4647; decide +kernel
      have hl : raw4647step0Labels = raw4647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4647 raw4647Labels permutation346 hz
    mixedMoment B raw4647step0 raw4647step0Labels = mixedMoment B raw4647step1 raw4647step1Labels := by
      have hz : ∀ j, raw4647step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4647step1 = (fun i j => raw4647step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4647step1 raw4647step0; decide +kernel
      have hl : raw4647step1Labels = raw4647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4647step0 raw4647step0Labels permutation56 hz
    mixedMoment B raw4647step1 raw4647step1Labels = mixedMoment B raw4647step2 raw4647step2Labels := by
      have ha : raw4647step2 = (fun i j => raw4647step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4647step2 raw4647step1; decide +kernel
      have hl : raw4647step2Labels = raw4647step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4647step1 raw4647step1Labels permutation29 permutation3
    mixedMoment B raw4647step2 raw4647step2Labels = mixedMoment B raw4647step3 raw4647step3Labels := by
      have ha : raw4647step3 = -raw4647step2 := by apply Matrix.ext; change ∀ i j, raw4647step3 i j = -(raw4647step2 i j); unfold raw4647step3 raw4647step2; decide +kernel
      have hl : raw4647step3Labels = raw4647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node813 node813Labels := by rfl

def raw4648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4648 raw4648Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw4648 raw4648Labels = mixedMoment B raw4648step0 raw4648step0Labels := by
      have hz : ∀ j, raw4648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4648step0 = (fun i j => raw4648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4648step0 raw4648; decide +kernel
      have hl : raw4648step0Labels = raw4648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4648 raw4648Labels permutation346 hz
    mixedMoment B raw4648step0 raw4648step0Labels = mixedMoment B raw4648step1 raw4648step1Labels := by
      have ha : raw4648step1 = (fun i j => raw4648step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4648step1 raw4648step0; decide +kernel
      have hl : raw4648step1Labels = raw4648step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4648step0 raw4648step0Labels permutation145 permutation2
    mixedMoment B raw4648step1 raw4648step1Labels = mixedMoment B raw4648step2 raw4648step2Labels := by
      have ha : raw4648step2 = -raw4648step1 := by apply Matrix.ext; change ∀ i j, raw4648step2 i j = -(raw4648step1 i j); unfold raw4648step2 raw4648step1; decide +kernel
      have hl : raw4648step2Labels = raw4648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw4649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4649 raw4649Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw4649 raw4649Labels = mixedMoment B raw4649step0 raw4649step0Labels := by
      have hz : ∀ j, raw4649 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4649step0 = (fun i j => raw4649 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4649step0 raw4649; decide +kernel
      have hl : raw4649step0Labels = raw4649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4649 raw4649Labels permutation265 hz
    mixedMoment B raw4649step0 raw4649step0Labels = mixedMoment B raw4649step1 raw4649step1Labels := by
      have ha : raw4649step1 = (fun i j => raw4649step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4649step1 raw4649step0; decide +kernel
      have hl : raw4649step1Labels = raw4649step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4649step0 raw4649step0Labels permutation145 permutation2
    mixedMoment B raw4649step1 raw4649step1Labels = mixedMoment B raw4649step2 raw4649step2Labels := by
      have ha : raw4649step2 = -raw4649step1 := by apply Matrix.ext; change ∀ i j, raw4649step2 i j = -(raw4649step1 i j); unfold raw4649step2 raw4649step1; decide +kernel
      have hl : raw4649step2Labels = raw4649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw4650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4650 raw4650Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw4650 raw4650Labels = mixedMoment B raw4650step0 raw4650step0Labels := by
      have hz : ∀ j, raw4650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4650step0 = (fun i j => raw4650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4650step0 raw4650; decide +kernel
      have hl : raw4650step0Labels = raw4650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4650 raw4650Labels permutation346 hz
    mixedMoment B raw4650step0 raw4650step0Labels = mixedMoment B raw4650step1 raw4650step1Labels := by
      have hz : ∀ j, raw4650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4650step1 = (fun i j => raw4650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4650step1 raw4650step0; decide +kernel
      have hl : raw4650step1Labels = raw4650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4650step0 raw4650step0Labels permutation56 hz
    mixedMoment B raw4650step1 raw4650step1Labels = mixedMoment B raw4650step2 raw4650step2Labels := by
      have ha : raw4650step2 = (fun i j => raw4650step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4650step2 raw4650step1; decide +kernel
      have hl : raw4650step2Labels = raw4650step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4650step1 raw4650step1Labels permutation31 permutation2
    mixedMoment B raw4650step2 raw4650step2Labels = mixedMoment B raw4650step3 raw4650step3Labels := by
      have ha : raw4650step3 = -raw4650step2 := by apply Matrix.ext; change ∀ i j, raw4650step3 i j = -(raw4650step2 i j); unfold raw4650step3 raw4650step2; decide +kernel
      have hl : raw4650step3Labels = raw4650step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw4651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4651step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4651 raw4651Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw4651 raw4651Labels = mixedMoment B raw4651step0 raw4651step0Labels := by
      have hz : ∀ j, raw4651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4651step0 = (fun i j => raw4651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4651step0 raw4651; decide +kernel
      have hl : raw4651step0Labels = raw4651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4651 raw4651Labels permutation346 hz
    mixedMoment B raw4651step0 raw4651step0Labels = mixedMoment B raw4651step1 raw4651step1Labels := by
      have hz : ∀ j, raw4651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4651step1 = (fun i j => raw4651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4651step1 raw4651step0; decide +kernel
      have hl : raw4651step1Labels = raw4651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4651step0 raw4651step0Labels permutation56 hz
    mixedMoment B raw4651step1 raw4651step1Labels = mixedMoment B raw4651step2 raw4651step2Labels := by
      have ha : raw4651step2 = (fun i j => raw4651step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4651step2 raw4651step1; decide +kernel
      have hl : raw4651step2Labels = raw4651step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4651step1 raw4651step1Labels permutation29 permutation2
    mixedMoment B raw4651step2 raw4651step2Labels = mixedMoment B raw4651step3 raw4651step3Labels := by
      have ha : raw4651step3 = -raw4651step2 := by apply Matrix.ext; change ∀ i j, raw4651step3 i j = -(raw4651step2 i j); unfold raw4651step3 raw4651step2; decide +kernel
      have hl : raw4651step3Labels = raw4651step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw4652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4652 raw4652Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw4652 raw4652Labels = mixedMoment B raw4652step0 raw4652step0Labels := by
      have hz : ∀ j, raw4652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4652step0 = (fun i j => raw4652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4652step0 raw4652; decide +kernel
      have hl : raw4652step0Labels = raw4652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4652 raw4652Labels permutation346 hz
    mixedMoment B raw4652step0 raw4652step0Labels = mixedMoment B raw4652step1 raw4652step1Labels := by
      have hz : ∀ j, raw4652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4652step1 = (fun i j => raw4652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4652step1 raw4652step0; decide +kernel
      have hl : raw4652step1Labels = raw4652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4652step0 raw4652step0Labels permutation56 hz
    mixedMoment B raw4652step1 raw4652step1Labels = mixedMoment B raw4652step2 raw4652step2Labels := by
      have ha : raw4652step2 = (fun i j => raw4652step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4652step2 raw4652step1; decide +kernel
      have hl : raw4652step2Labels = raw4652step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4652step1 raw4652step1Labels permutation29 permutation7
    mixedMoment B raw4652step2 raw4652step2Labels = mixedMoment B raw4652step3 raw4652step3Labels := by
      have ha : raw4652step3 = raw4652step2 := by apply Matrix.ext; unfold raw4652step3 raw4652step2; decide +kernel
      have hl : raw4652step2Labels = labelEmbedding10 ∘ raw4652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4652step2 raw4652step2Labels raw4652step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw4653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4653 raw4653Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw4653 raw4653Labels = mixedMoment B raw4653step0 raw4653step0Labels := by
      have hz : ∀ j, raw4653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4653step0 = (fun i j => raw4653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4653step0 raw4653; decide +kernel
      have hl : raw4653step0Labels = raw4653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4653 raw4653Labels permutation346 hz
    mixedMoment B raw4653step0 raw4653step0Labels = mixedMoment B raw4653step1 raw4653step1Labels := by
      have ha : raw4653step1 = (fun i j => raw4653step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4653step1 raw4653step0; decide +kernel
      have hl : raw4653step1Labels = raw4653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4653step0 raw4653step0Labels permutation40 permutation3
    mixedMoment B raw4653step1 raw4653step1Labels = mixedMoment B raw4653step2 raw4653step2Labels := by
      have ha : raw4653step2 = raw4653step1 := by apply Matrix.ext; unfold raw4653step2 raw4653step1; decide +kernel
      have hl : raw4653step1Labels = labelEmbedding6 ∘ raw4653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4653step1 raw4653step1Labels raw4653step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw4654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4654 raw4654Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw4654 raw4654Labels = mixedMoment B raw4654step0 raw4654step0Labels := by
      have ha : raw4654step0 = (fun i j => raw4654 (permutation616 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4654step0 raw4654; decide +kernel
      have hl : raw4654step0Labels = raw4654Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4654 raw4654Labels permutation616 permutation2
    mixedMoment B raw4654step0 raw4654step0Labels = mixedMoment B raw4654step1 raw4654step1Labels := by
      have ha : raw4654step1 = -raw4654step0 := by apply Matrix.ext; change ∀ i j, raw4654step1 i j = -(raw4654step0 i j); unfold raw4654step1 raw4654step0; decide +kernel
      have hl : raw4654step1Labels = raw4654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw4655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4655 raw4655Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4655 raw4655Labels = mixedMoment B raw4655step0 raw4655step0Labels := by
      have hz : ∀ j, raw4655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4655step0 = (fun i j => raw4655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4655step0 raw4655; decide +kernel
      have hl : raw4655step0Labels = raw4655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4655 raw4655Labels permutation346 hz
    mixedMoment B raw4655step0 raw4655step0Labels = mixedMoment B raw4655step1 raw4655step1Labels := by
      have ha : raw4655step1 = (fun i j => raw4655step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4655step1 raw4655step0; decide +kernel
      have hl : raw4655step1Labels = raw4655step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4655step0 raw4655step0Labels permutation139 permutation2
    mixedMoment B raw4655step1 raw4655step1Labels = mixedMoment B raw4655step2 raw4655step2Labels := by
      have ha : raw4655step2 = -raw4655step1 := by apply Matrix.ext; change ∀ i j, raw4655step2 i j = -(raw4655step1 i j); unfold raw4655step2 raw4655step1; decide +kernel
      have hl : raw4655step2Labels = raw4655step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4656 raw4656Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4656 raw4656Labels = mixedMoment B raw4656step0 raw4656step0Labels := by
      have hz : ∀ j, raw4656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4656step0 = (fun i j => raw4656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4656step0 raw4656; decide +kernel
      have hl : raw4656step0Labels = raw4656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4656 raw4656Labels permutation346 hz
    mixedMoment B raw4656step0 raw4656step0Labels = mixedMoment B raw4656step1 raw4656step1Labels := by
      have ha : raw4656step1 = (fun i j => raw4656step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4656step1 raw4656step0; decide +kernel
      have hl : raw4656step1Labels = raw4656step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4656step0 raw4656step0Labels permutation137 permutation2
    mixedMoment B raw4656step1 raw4656step1Labels = mixedMoment B raw4656step2 raw4656step2Labels := by
      have ha : raw4656step2 = -raw4656step1 := by apply Matrix.ext; change ∀ i j, raw4656step2 i j = -(raw4656step1 i j); unfold raw4656step2 raw4656step1; decide +kernel
      have hl : raw4656step2Labels = raw4656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4657 raw4657Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw4657 raw4657Labels = mixedMoment B raw4657step0 raw4657step0Labels := by
      have hz : ∀ j, raw4657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4657step0 = (fun i j => raw4657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4657step0 raw4657; decide +kernel
      have hl : raw4657step0Labels = raw4657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4657 raw4657Labels permutation346 hz
    mixedMoment B raw4657step0 raw4657step0Labels = mixedMoment B raw4657step1 raw4657step1Labels := by
      have ha : raw4657step1 = (fun i j => raw4657step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4657step1 raw4657step0; decide +kernel
      have hl : raw4657step1Labels = raw4657step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4657step0 raw4657step0Labels permutation137 permutation7
    mixedMoment B raw4657step1 raw4657step1Labels = mixedMoment B raw4657step2 raw4657step2Labels := by
      have ha : raw4657step2 = raw4657step1 := by apply Matrix.ext; unfold raw4657step2 raw4657step1; decide +kernel
      have hl : raw4657step1Labels = labelEmbedding10 ∘ raw4657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4657step1 raw4657step1Labels raw4657step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw4658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4658 raw4658Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw4658 raw4658Labels = mixedMoment B raw4658step0 raw4658step0Labels := by
      have hz : ∀ j, raw4658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4658step0 = (fun i j => raw4658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4658step0 raw4658; decide +kernel
      have hl : raw4658step0Labels = raw4658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4658 raw4658Labels permutation265 hz
    mixedMoment B raw4658step0 raw4658step0Labels = mixedMoment B raw4658step1 raw4658step1Labels := by
      have ha : raw4658step1 = (fun i j => raw4658step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4658step1 raw4658step0; decide +kernel
      have hl : raw4658step1Labels = raw4658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4658step0 raw4658step0Labels permutation40 permutation3
    mixedMoment B raw4658step1 raw4658step1Labels = mixedMoment B raw4658step2 raw4658step2Labels := by
      have ha : raw4658step2 = raw4658step1 := by apply Matrix.ext; unfold raw4658step2 raw4658step1; decide +kernel
      have hl : raw4658step1Labels = labelEmbedding6 ∘ raw4658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4658step1 raw4658step1Labels raw4658step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw4659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4659 raw4659Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw4659 raw4659Labels = mixedMoment B raw4659step0 raw4659step0Labels := by
      have ha : raw4659step0 = (fun i j => raw4659 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4659step0 raw4659; decide +kernel
      have hl : raw4659step0Labels = raw4659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4659 raw4659Labels permutation640 permutation2
    mixedMoment B raw4659step0 raw4659step0Labels = mixedMoment B raw4659step1 raw4659step1Labels := by
      have ha : raw4659step1 = -raw4659step0 := by apply Matrix.ext; change ∀ i j, raw4659step1 i j = -(raw4659step0 i j); unfold raw4659step1 raw4659step0; decide +kernel
      have hl : raw4659step1Labels = raw4659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw4660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4660 raw4660Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4660 raw4660Labels = mixedMoment B raw4660step0 raw4660step0Labels := by
      have hz : ∀ j, raw4660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4660step0 = (fun i j => raw4660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4660step0 raw4660; decide +kernel
      have hl : raw4660step0Labels = raw4660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4660 raw4660Labels permutation265 hz
    mixedMoment B raw4660step0 raw4660step0Labels = mixedMoment B raw4660step1 raw4660step1Labels := by
      have ha : raw4660step1 = (fun i j => raw4660step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4660step1 raw4660step0; decide +kernel
      have hl : raw4660step1Labels = raw4660step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4660step0 raw4660step0Labels permutation139 permutation2
    mixedMoment B raw4660step1 raw4660step1Labels = mixedMoment B raw4660step2 raw4660step2Labels := by
      have ha : raw4660step2 = -raw4660step1 := by apply Matrix.ext; change ∀ i j, raw4660step2 i j = -(raw4660step1 i j); unfold raw4660step2 raw4660step1; decide +kernel
      have hl : raw4660step2Labels = raw4660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4661 raw4661Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw4661 raw4661Labels = mixedMoment B raw4661step0 raw4661step0Labels := by
      have hz : ∀ j, raw4661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4661step0 = (fun i j => raw4661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4661step0 raw4661; decide +kernel
      have hl : raw4661step0Labels = raw4661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4661 raw4661Labels permutation265 hz
    mixedMoment B raw4661step0 raw4661step0Labels = mixedMoment B raw4661step1 raw4661step1Labels := by
      have ha : raw4661step1 = (fun i j => raw4661step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4661step1 raw4661step0; decide +kernel
      have hl : raw4661step1Labels = raw4661step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4661step0 raw4661step0Labels permutation137 permutation2
    mixedMoment B raw4661step1 raw4661step1Labels = mixedMoment B raw4661step2 raw4661step2Labels := by
      have ha : raw4661step2 = -raw4661step1 := by apply Matrix.ext; change ∀ i j, raw4661step2 i j = -(raw4661step1 i j); unfold raw4661step2 raw4661step1; decide +kernel
      have hl : raw4661step2Labels = raw4661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw4662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4662step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4662 raw4662Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw4662 raw4662Labels = mixedMoment B raw4662step0 raw4662step0Labels := by
      have hz : ∀ j, raw4662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4662step0 = (fun i j => raw4662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4662step0 raw4662; decide +kernel
      have hl : raw4662step0Labels = raw4662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4662 raw4662Labels permutation265 hz
    mixedMoment B raw4662step0 raw4662step0Labels = mixedMoment B raw4662step1 raw4662step1Labels := by
      have ha : raw4662step1 = (fun i j => raw4662step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4662step1 raw4662step0; decide +kernel
      have hl : raw4662step1Labels = raw4662step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4662step0 raw4662step0Labels permutation137 permutation7
    mixedMoment B raw4662step1 raw4662step1Labels = mixedMoment B raw4662step2 raw4662step2Labels := by
      have ha : raw4662step2 = raw4662step1 := by apply Matrix.ext; unfold raw4662step2 raw4662step1; decide +kernel
      have hl : raw4662step1Labels = labelEmbedding10 ∘ raw4662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4662step1 raw4662step1Labels raw4662step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw4663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4663 raw4663Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw4663 raw4663Labels = mixedMoment B raw4663step0 raw4663step0Labels := by
      have hz : ∀ j, raw4663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4663step0 = (fun i j => raw4663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4663step0 raw4663; decide +kernel
      have hl : raw4663step0Labels = raw4663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4663 raw4663Labels permutation346 hz
    mixedMoment B raw4663step0 raw4663step0Labels = mixedMoment B raw4663step1 raw4663step1Labels := by
      have hz : ∀ j, raw4663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4663step1 = (fun i j => raw4663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4663step1 raw4663step0; decide +kernel
      have hl : raw4663step1Labels = raw4663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4663step0 raw4663step0Labels permutation56 hz
    mixedMoment B raw4663step1 raw4663step1Labels = mixedMoment B raw4663step2 raw4663step2Labels := by
      have ha : raw4663step2 = (fun i j => raw4663step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4663step2 raw4663step1; decide +kernel
      have hl : raw4663step2Labels = raw4663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4663step1 raw4663step1Labels permutation10 permutation3
    mixedMoment B raw4663step2 raw4663step2Labels = mixedMoment B raw4663step3 raw4663step3Labels := by
      have ha : raw4663step3 = raw4663step2 := by apply Matrix.ext; unfold raw4663step3 raw4663step2; decide +kernel
      have hl : raw4663step2Labels = labelEmbedding6 ∘ raw4663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4663step2 raw4663step2Labels raw4663step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw4664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4664 raw4664Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw4664 raw4664Labels = mixedMoment B raw4664step0 raw4664step0Labels := by
      have hz : ∀ j, raw4664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4664step0 = (fun i j => raw4664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4664step0 raw4664; decide +kernel
      have hl : raw4664step0Labels = raw4664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4664 raw4664Labels permutation346 hz
    mixedMoment B raw4664step0 raw4664step0Labels = mixedMoment B raw4664step1 raw4664step1Labels := by
      have ha : raw4664step1 = (fun i j => raw4664step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4664step1 raw4664step0; decide +kernel
      have hl : raw4664step1Labels = raw4664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4664step0 raw4664step0Labels permutation145 permutation2
    mixedMoment B raw4664step1 raw4664step1Labels = mixedMoment B raw4664step2 raw4664step2Labels := by
      have ha : raw4664step2 = -raw4664step1 := by apply Matrix.ext; change ∀ i j, raw4664step2 i j = -(raw4664step1 i j); unfold raw4664step2 raw4664step1; decide +kernel
      have hl : raw4664step2Labels = raw4664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw4665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4665 raw4665Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw4665 raw4665Labels = mixedMoment B raw4665step0 raw4665step0Labels := by
      have hz : ∀ j, raw4665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4665step0 = (fun i j => raw4665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4665step0 raw4665; decide +kernel
      have hl : raw4665step0Labels = raw4665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4665 raw4665Labels permutation265 hz
    mixedMoment B raw4665step0 raw4665step0Labels = mixedMoment B raw4665step1 raw4665step1Labels := by
      have ha : raw4665step1 = (fun i j => raw4665step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4665step1 raw4665step0; decide +kernel
      have hl : raw4665step1Labels = raw4665step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4665step0 raw4665step0Labels permutation145 permutation2
    mixedMoment B raw4665step1 raw4665step1Labels = mixedMoment B raw4665step2 raw4665step2Labels := by
      have ha : raw4665step2 = -raw4665step1 := by apply Matrix.ext; change ∀ i j, raw4665step2 i j = -(raw4665step1 i j); unfold raw4665step2 raw4665step1; decide +kernel
      have hl : raw4665step2Labels = raw4665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw4666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4666 raw4666Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4666 raw4666Labels = mixedMoment B raw4666step0 raw4666step0Labels := by
      have hz : ∀ j, raw4666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4666step0 = (fun i j => raw4666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4666step0 raw4666; decide +kernel
      have hl : raw4666step0Labels = raw4666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4666 raw4666Labels permutation346 hz
    mixedMoment B raw4666step0 raw4666step0Labels = mixedMoment B raw4666step1 raw4666step1Labels := by
      have hz : ∀ j, raw4666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4666step1 = (fun i j => raw4666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4666step1 raw4666step0; decide +kernel
      have hl : raw4666step1Labels = raw4666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4666step0 raw4666step0Labels permutation56 hz
    mixedMoment B raw4666step1 raw4666step1Labels = mixedMoment B raw4666step2 raw4666step2Labels := by
      have ha : raw4666step2 = (fun i j => raw4666step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4666step2 raw4666step1; decide +kernel
      have hl : raw4666step2Labels = raw4666step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4666step1 raw4666step1Labels permutation29 permutation2
    mixedMoment B raw4666step2 raw4666step2Labels = mixedMoment B raw4666step3 raw4666step3Labels := by
      have ha : raw4666step3 = -raw4666step2 := by apply Matrix.ext; change ∀ i j, raw4666step3 i j = -(raw4666step2 i j); unfold raw4666step3 raw4666step2; decide +kernel
      have hl : raw4666step3Labels = raw4666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw4667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4667 raw4667Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw4667 raw4667Labels = mixedMoment B raw4667step0 raw4667step0Labels := by
      have hz : ∀ j, raw4667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4667step0 = (fun i j => raw4667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4667step0 raw4667; decide +kernel
      have hl : raw4667step0Labels = raw4667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4667 raw4667Labels permutation346 hz
    mixedMoment B raw4667step0 raw4667step0Labels = mixedMoment B raw4667step1 raw4667step1Labels := by
      have hz : ∀ j, raw4667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4667step1 = (fun i j => raw4667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4667step1 raw4667step0; decide +kernel
      have hl : raw4667step1Labels = raw4667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4667step0 raw4667step0Labels permutation56 hz
    mixedMoment B raw4667step1 raw4667step1Labels = mixedMoment B raw4667step2 raw4667step2Labels := by
      have ha : raw4667step2 = (fun i j => raw4667step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4667step2 raw4667step1; decide +kernel
      have hl : raw4667step2Labels = raw4667step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4667step1 raw4667step1Labels permutation10 permutation3
    mixedMoment B raw4667step2 raw4667step2Labels = mixedMoment B raw4667step3 raw4667step3Labels := by
      have ha : raw4667step3 = raw4667step2 := by apply Matrix.ext; unfold raw4667step3 raw4667step2; decide +kernel
      have hl : raw4667step2Labels = labelEmbedding6 ∘ raw4667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4667step2 raw4667step2Labels raw4667step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw4668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4668 raw4668Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw4668 raw4668Labels = mixedMoment B raw4668step0 raw4668step0Labels := by
      have hz : ∀ j, raw4668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4668step0 = (fun i j => raw4668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4668step0 raw4668; decide +kernel
      have hl : raw4668step0Labels = raw4668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4668 raw4668Labels permutation346 hz
    mixedMoment B raw4668step0 raw4668step0Labels = mixedMoment B raw4668step1 raw4668step1Labels := by
      have hz : ∀ j, raw4668step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4668step1 = (fun i j => raw4668step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4668step1 raw4668step0; decide +kernel
      have hl : raw4668step1Labels = raw4668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4668step0 raw4668step0Labels permutation56 hz
    mixedMoment B raw4668step1 raw4668step1Labels = mixedMoment B raw4668step2 raw4668step2Labels := by
      have ha : raw4668step2 = (fun i j => raw4668step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4668step2 raw4668step1; decide +kernel
      have hl : raw4668step2Labels = raw4668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4668step1 raw4668step1Labels permutation8 permutation3
    mixedMoment B raw4668step2 raw4668step2Labels = mixedMoment B raw4668step3 raw4668step3Labels := by
      have ha : raw4668step3 = raw4668step2 := by apply Matrix.ext; unfold raw4668step3 raw4668step2; decide +kernel
      have hl : raw4668step2Labels = labelEmbedding6 ∘ raw4668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4668step2 raw4668step2Labels raw4668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw4669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4669 raw4669Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw4669 raw4669Labels = mixedMoment B raw4669step0 raw4669step0Labels := by
      have hz : ∀ j, raw4669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4669step0 = (fun i j => raw4669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4669step0 raw4669; decide +kernel
      have hl : raw4669step0Labels = raw4669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4669 raw4669Labels permutation346 hz
    mixedMoment B raw4669step0 raw4669step0Labels = mixedMoment B raw4669step1 raw4669step1Labels := by
      have ha : raw4669step1 = (fun i j => raw4669step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4669step1 raw4669step0; decide +kernel
      have hl : raw4669step1Labels = raw4669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4669step0 raw4669step0Labels permutation151 permutation2
    mixedMoment B raw4669step1 raw4669step1Labels = mixedMoment B raw4669step2 raw4669step2Labels := by
      have ha : raw4669step2 = -raw4669step1 := by apply Matrix.ext; change ∀ i j, raw4669step2 i j = -(raw4669step1 i j); unfold raw4669step2 raw4669step1; decide +kernel
      have hl : raw4669step2Labels = raw4669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw4670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4670 raw4670Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw4670 raw4670Labels = mixedMoment B raw4670step0 raw4670step0Labels := by
      have hz : ∀ j, raw4670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4670step0 = (fun i j => raw4670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4670step0 raw4670; decide +kernel
      have hl : raw4670step0Labels = raw4670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4670 raw4670Labels permutation265 hz
    mixedMoment B raw4670step0 raw4670step0Labels = mixedMoment B raw4670step1 raw4670step1Labels := by
      have ha : raw4670step1 = (fun i j => raw4670step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4670step1 raw4670step0; decide +kernel
      have hl : raw4670step1Labels = raw4670step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4670step0 raw4670step0Labels permutation151 permutation2
    mixedMoment B raw4670step1 raw4670step1Labels = mixedMoment B raw4670step2 raw4670step2Labels := by
      have ha : raw4670step2 = -raw4670step1 := by apply Matrix.ext; change ∀ i j, raw4670step2 i j = -(raw4670step1 i j); unfold raw4670step2 raw4670step1; decide +kernel
      have hl : raw4670step2Labels = raw4670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw4671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4671step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4671 raw4671Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw4671 raw4671Labels = mixedMoment B raw4671step0 raw4671step0Labels := by
      have hz : ∀ j, raw4671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4671step0 = (fun i j => raw4671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4671step0 raw4671; decide +kernel
      have hl : raw4671step0Labels = raw4671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4671 raw4671Labels permutation346 hz
    mixedMoment B raw4671step0 raw4671step0Labels = mixedMoment B raw4671step1 raw4671step1Labels := by
      have hz : ∀ j, raw4671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4671step1 = (fun i j => raw4671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4671step1 raw4671step0; decide +kernel
      have hl : raw4671step1Labels = raw4671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4671step0 raw4671step0Labels permutation56 hz
    mixedMoment B raw4671step1 raw4671step1Labels = mixedMoment B raw4671step2 raw4671step2Labels := by
      have ha : raw4671step2 = (fun i j => raw4671step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4671step2 raw4671step1; decide +kernel
      have hl : raw4671step2Labels = raw4671step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4671step1 raw4671step1Labels permutation31 permutation2
    mixedMoment B raw4671step2 raw4671step2Labels = mixedMoment B raw4671step3 raw4671step3Labels := by
      have ha : raw4671step3 = -raw4671step2 := by apply Matrix.ext; change ∀ i j, raw4671step3 i j = -(raw4671step2 i j); unfold raw4671step3 raw4671step2; decide +kernel
      have hl : raw4671step3Labels = raw4671step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw4672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4672step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4672step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4672 raw4672Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw4672 raw4672Labels = mixedMoment B raw4672step0 raw4672step0Labels := by
      have hz : ∀ j, raw4672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4672step0 = (fun i j => raw4672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4672step0 raw4672; decide +kernel
      have hl : raw4672step0Labels = raw4672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4672 raw4672Labels permutation346 hz
    mixedMoment B raw4672step0 raw4672step0Labels = mixedMoment B raw4672step1 raw4672step1Labels := by
      have hz : ∀ j, raw4672step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4672step1 = (fun i j => raw4672step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4672step1 raw4672step0; decide +kernel
      have hl : raw4672step1Labels = raw4672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4672step0 raw4672step0Labels permutation56 hz
    mixedMoment B raw4672step1 raw4672step1Labels = mixedMoment B raw4672step2 raw4672step2Labels := by
      have ha : raw4672step2 = (fun i j => raw4672step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4672step2 raw4672step1; decide +kernel
      have hl : raw4672step2Labels = raw4672step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4672step1 raw4672step1Labels permutation8 permutation3
    mixedMoment B raw4672step2 raw4672step2Labels = mixedMoment B raw4672step3 raw4672step3Labels := by
      have ha : raw4672step3 = raw4672step2 := by apply Matrix.ext; unfold raw4672step3 raw4672step2; decide +kernel
      have hl : raw4672step2Labels = labelEmbedding6 ∘ raw4672step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4672step2 raw4672step2Labels raw4672step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw4673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw4673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4673 raw4673Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw4673 raw4673Labels = mixedMoment B raw4673step0 raw4673step0Labels := by
      have hz : ∀ j, raw4673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4673step0 = (fun i j => raw4673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4673step0 raw4673; decide +kernel
      have hl : raw4673step0Labels = raw4673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4673 raw4673Labels permutation346 hz
    mixedMoment B raw4673step0 raw4673step0Labels = mixedMoment B raw4673step1 raw4673step1Labels := by
      have hz : ∀ j, raw4673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4673step1 = (fun i j => raw4673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4673step1 raw4673step0; decide +kernel
      have hl : raw4673step1Labels = raw4673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4673step0 raw4673step0Labels permutation56 hz
    mixedMoment B raw4673step1 raw4673step1Labels = mixedMoment B raw4673step2 raw4673step2Labels := by
      have ha : raw4673step2 = (fun i j => raw4673step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4673step2 raw4673step1; decide +kernel
      have hl : raw4673step2Labels = raw4673step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4673step1 raw4673step1Labels permutation29 permutation2
    mixedMoment B raw4673step2 raw4673step2Labels = mixedMoment B raw4673step3 raw4673step3Labels := by
      have ha : raw4673step3 = -raw4673step2 := by apply Matrix.ext; change ∀ i j, raw4673step3 i j = -(raw4673step2 i j); unfold raw4673step3 raw4673step2; decide +kernel
      have hl : raw4673step3Labels = raw4673step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw4674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4674 raw4674Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw4674 raw4674Labels = mixedMoment B raw4674step0 raw4674step0Labels := by
      have hz : ∀ j, raw4674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4674step0 = (fun i j => raw4674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4674step0 raw4674; decide +kernel
      have hl : raw4674step0Labels = raw4674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4674 raw4674Labels permutation346 hz
    mixedMoment B raw4674step0 raw4674step0Labels = mixedMoment B raw4674step1 raw4674step1Labels := by
      have ha : raw4674step1 = (fun i j => raw4674step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4674step1 raw4674step0; decide +kernel
      have hl : raw4674step1Labels = raw4674step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4674step0 raw4674step0Labels permutation145 permutation2
    mixedMoment B raw4674step1 raw4674step1Labels = mixedMoment B raw4674step2 raw4674step2Labels := by
      have ha : raw4674step2 = -raw4674step1 := by apply Matrix.ext; change ∀ i j, raw4674step2 i j = -(raw4674step1 i j); unfold raw4674step2 raw4674step1; decide +kernel
      have hl : raw4674step2Labels = raw4674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw4675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4675 raw4675Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw4675 raw4675Labels = mixedMoment B raw4675step0 raw4675step0Labels := by
      have hz : ∀ j, raw4675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4675step0 = (fun i j => raw4675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4675step0 raw4675; decide +kernel
      have hl : raw4675step0Labels = raw4675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4675 raw4675Labels permutation265 hz
    mixedMoment B raw4675step0 raw4675step0Labels = mixedMoment B raw4675step1 raw4675step1Labels := by
      have ha : raw4675step1 = (fun i j => raw4675step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4675step1 raw4675step0; decide +kernel
      have hl : raw4675step1Labels = raw4675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4675step0 raw4675step0Labels permutation145 permutation2
    mixedMoment B raw4675step1 raw4675step1Labels = mixedMoment B raw4675step2 raw4675step2Labels := by
      have ha : raw4675step2 = -raw4675step1 := by apply Matrix.ext; change ∀ i j, raw4675step2 i j = -(raw4675step1 i j); unfold raw4675step2 raw4675step1; decide +kernel
      have hl : raw4675step2Labels = raw4675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw4676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4676step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4676 raw4676Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw4676 raw4676Labels = mixedMoment B raw4676step0 raw4676step0Labels := by
      have hz : ∀ j, raw4676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4676step0 = (fun i j => raw4676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4676step0 raw4676; decide +kernel
      have hl : raw4676step0Labels = raw4676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4676 raw4676Labels permutation346 hz
    mixedMoment B raw4676step0 raw4676step0Labels = mixedMoment B raw4676step1 raw4676step1Labels := by
      have hz : ∀ j, raw4676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4676step1 = (fun i j => raw4676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4676step1 raw4676step0; decide +kernel
      have hl : raw4676step1Labels = raw4676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4676step0 raw4676step0Labels permutation56 hz
    mixedMoment B raw4676step1 raw4676step1Labels = mixedMoment B raw4676step2 raw4676step2Labels := by
      have ha : raw4676step2 = (fun i j => raw4676step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4676step2 raw4676step1; decide +kernel
      have hl : raw4676step2Labels = raw4676step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4676step1 raw4676step1Labels permutation31 permutation2
    mixedMoment B raw4676step2 raw4676step2Labels = mixedMoment B raw4676step3 raw4676step3Labels := by
      have ha : raw4676step3 = -raw4676step2 := by apply Matrix.ext; change ∀ i j, raw4676step3 i j = -(raw4676step2 i j); unfold raw4676step3 raw4676step2; decide +kernel
      have hl : raw4676step3Labels = raw4676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw4677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4677 raw4677Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw4677 raw4677Labels = mixedMoment B raw4677step0 raw4677step0Labels := by
      have hz : ∀ j, raw4677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4677step0 = (fun i j => raw4677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4677step0 raw4677; decide +kernel
      have hl : raw4677step0Labels = raw4677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4677 raw4677Labels permutation346 hz
    mixedMoment B raw4677step0 raw4677step0Labels = mixedMoment B raw4677step1 raw4677step1Labels := by
      have hz : ∀ j, raw4677step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4677step1 = (fun i j => raw4677step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4677step1 raw4677step0; decide +kernel
      have hl : raw4677step1Labels = raw4677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4677step0 raw4677step0Labels permutation56 hz
    mixedMoment B raw4677step1 raw4677step1Labels = mixedMoment B raw4677step2 raw4677step2Labels := by
      have ha : raw4677step2 = (fun i j => raw4677step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4677step2 raw4677step1; decide +kernel
      have hl : raw4677step2Labels = raw4677step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4677step1 raw4677step1Labels permutation29 permutation2
    mixedMoment B raw4677step2 raw4677step2Labels = mixedMoment B raw4677step3 raw4677step3Labels := by
      have ha : raw4677step3 = -raw4677step2 := by apply Matrix.ext; change ∀ i j, raw4677step3 i j = -(raw4677step2 i j); unfold raw4677step3 raw4677step2; decide +kernel
      have hl : raw4677step3Labels = raw4677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw4678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4678 raw4678Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw4678 raw4678Labels = mixedMoment B raw4678step0 raw4678step0Labels := by
      have hz : ∀ j, raw4678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4678step0 = (fun i j => raw4678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4678step0 raw4678; decide +kernel
      have hl : raw4678step0Labels = raw4678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4678 raw4678Labels permutation346 hz
    mixedMoment B raw4678step0 raw4678step0Labels = mixedMoment B raw4678step1 raw4678step1Labels := by
      have ha : raw4678step1 = (fun i j => raw4678step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4678step1 raw4678step0; decide +kernel
      have hl : raw4678step1Labels = raw4678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4678step0 raw4678step0Labels permutation145 permutation3
    mixedMoment B raw4678step1 raw4678step1Labels = mixedMoment B raw4678step2 raw4678step2Labels := by
      have ha : raw4678step2 = -raw4678step1 := by apply Matrix.ext; change ∀ i j, raw4678step2 i j = -(raw4678step1 i j); unfold raw4678step2 raw4678step1; decide +kernel
      have hl : raw4678step2Labels = raw4678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw4679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw4679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw4679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4679 raw4679Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw4679 raw4679Labels = mixedMoment B raw4679step0 raw4679step0Labels := by
      have hz : ∀ j, raw4679 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4679step0 = (fun i j => raw4679 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4679step0 raw4679; decide +kernel
      have hl : raw4679step0Labels = raw4679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4679 raw4679Labels permutation265 hz
    mixedMoment B raw4679step0 raw4679step0Labels = mixedMoment B raw4679step1 raw4679step1Labels := by
      have ha : raw4679step1 = (fun i j => raw4679step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4679step1 raw4679step0; decide +kernel
      have hl : raw4679step1Labels = raw4679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4679step0 raw4679step0Labels permutation145 permutation3
    mixedMoment B raw4679step1 raw4679step1Labels = mixedMoment B raw4679step2 raw4679step2Labels := by
      have ha : raw4679step2 = -raw4679step1 := by apply Matrix.ext; change ∀ i j, raw4679step2 i j = -(raw4679step1 i j); unfold raw4679step2 raw4679step1; decide +kernel
      have hl : raw4679step2Labels = raw4679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw4680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4680step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4680step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4680 raw4680Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw4680 raw4680Labels = mixedMoment B raw4680step0 raw4680step0Labels := by
      have hz : ∀ j, raw4680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4680step0 = (fun i j => raw4680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4680step0 raw4680; decide +kernel
      have hl : raw4680step0Labels = raw4680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4680 raw4680Labels permutation346 hz
    mixedMoment B raw4680step0 raw4680step0Labels = mixedMoment B raw4680step1 raw4680step1Labels := by
      have hz : ∀ j, raw4680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4680step1 = (fun i j => raw4680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4680step1 raw4680step0; decide +kernel
      have hl : raw4680step1Labels = raw4680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4680step0 raw4680step0Labels permutation56 hz
    mixedMoment B raw4680step1 raw4680step1Labels = mixedMoment B raw4680step2 raw4680step2Labels := by
      have ha : raw4680step2 = (fun i j => raw4680step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4680step2 raw4680step1; decide +kernel
      have hl : raw4680step2Labels = raw4680step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4680step1 raw4680step1Labels permutation31 permutation3
    mixedMoment B raw4680step2 raw4680step2Labels = mixedMoment B raw4680step3 raw4680step3Labels := by
      have ha : raw4680step3 = -raw4680step2 := by apply Matrix.ext; change ∀ i j, raw4680step3 i j = -(raw4680step2 i j); unfold raw4680step3 raw4680step2; decide +kernel
      have hl : raw4680step3Labels = raw4680step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw4681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4681step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw4681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw4681step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4681 raw4681Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw4681 raw4681Labels = mixedMoment B raw4681step0 raw4681step0Labels := by
      have hz : ∀ j, raw4681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4681step0 = (fun i j => raw4681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4681step0 raw4681; decide +kernel
      have hl : raw4681step0Labels = raw4681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4681 raw4681Labels permutation346 hz
    mixedMoment B raw4681step0 raw4681step0Labels = mixedMoment B raw4681step1 raw4681step1Labels := by
      have hz : ∀ j, raw4681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4681step1 = (fun i j => raw4681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4681step1 raw4681step0; decide +kernel
      have hl : raw4681step1Labels = raw4681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4681step0 raw4681step0Labels permutation56 hz
    mixedMoment B raw4681step1 raw4681step1Labels = mixedMoment B raw4681step2 raw4681step2Labels := by
      have ha : raw4681step2 = (fun i j => raw4681step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4681step2 raw4681step1; decide +kernel
      have hl : raw4681step2Labels = raw4681step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4681step1 raw4681step1Labels permutation29 permutation3
    mixedMoment B raw4681step2 raw4681step2Labels = mixedMoment B raw4681step3 raw4681step3Labels := by
      have ha : raw4681step3 = -raw4681step2 := by apply Matrix.ext; change ∀ i j, raw4681step3 i j = -(raw4681step2 i j); unfold raw4681step3 raw4681step2; decide +kernel
      have hl : raw4681step3Labels = raw4681step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw4682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw4682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4682 raw4682Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw4682 raw4682Labels = mixedMoment B raw4682step0 raw4682step0Labels := by
      have hz : ∀ j, raw4682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4682step0 = (fun i j => raw4682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4682step0 raw4682; decide +kernel
      have hl : raw4682step0Labels = raw4682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4682 raw4682Labels permutation346 hz
    mixedMoment B raw4682step0 raw4682step0Labels = mixedMoment B raw4682step1 raw4682step1Labels := by
      have hz : ∀ j, raw4682step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4682step1 = (fun i j => raw4682step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4682step1 raw4682step0; decide +kernel
      have hl : raw4682step1Labels = raw4682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4682step0 raw4682step0Labels permutation56 hz
    mixedMoment B raw4682step1 raw4682step1Labels = mixedMoment B raw4682step2 raw4682step2Labels := by
      have ha : raw4682step2 = (fun i j => raw4682step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4682step2 raw4682step1; decide +kernel
      have hl : raw4682step2Labels = raw4682step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4682step1 raw4682step1Labels permutation26 permutation6
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw4683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4683 raw4683Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw4683 raw4683Labels = mixedMoment B raw4683step0 raw4683step0Labels := by
      have hz : ∀ j, raw4683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4683step0 = (fun i j => raw4683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4683step0 raw4683; decide +kernel
      have hl : raw4683step0Labels = raw4683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4683 raw4683Labels permutation346 hz
    mixedMoment B raw4683step0 raw4683step0Labels = mixedMoment B raw4683step1 raw4683step1Labels := by
      have ha : raw4683step1 = (fun i j => raw4683step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4683step1 raw4683step0; decide +kernel
      have hl : raw4683step1Labels = raw4683step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4683step0 raw4683step0Labels permutation40 permutation3
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw4684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4684 raw4684Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw4684 raw4684Labels = mixedMoment B raw4684step0 raw4684step0Labels := by
      have ha : raw4684step0 = (fun i j => raw4684 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4684step0 raw4684; decide +kernel
      have hl : raw4684step0Labels = raw4684Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4684 raw4684Labels permutation184 permutation3
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw4685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4685 raw4685Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw4685 raw4685Labels = mixedMoment B raw4685step0 raw4685step0Labels := by
      have hz : ∀ j, raw4685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4685step0 = (fun i j => raw4685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4685step0 raw4685; decide +kernel
      have hl : raw4685step0Labels = raw4685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4685 raw4685Labels permutation346 hz
    mixedMoment B raw4685step0 raw4685step0Labels = mixedMoment B raw4685step1 raw4685step1Labels := by
      have ha : raw4685step1 = (fun i j => raw4685step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4685step1 raw4685step0; decide +kernel
      have hl : raw4685step1Labels = raw4685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4685step0 raw4685step0Labels permutation40 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw4686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4686 raw4686Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw4686 raw4686Labels = mixedMoment B raw4686step0 raw4686step0Labels := by
      have hz : ∀ j, raw4686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4686step0 = (fun i j => raw4686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4686step0 raw4686; decide +kernel
      have hl : raw4686step0Labels = raw4686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4686 raw4686Labels permutation346 hz
    mixedMoment B raw4686step0 raw4686step0Labels = mixedMoment B raw4686step1 raw4686step1Labels := by
      have ha : raw4686step1 = (fun i j => raw4686step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4686step1 raw4686step0; decide +kernel
      have hl : raw4686step1Labels = raw4686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4686step0 raw4686step0Labels permutation46 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw4687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4687 raw4687Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw4687 raw4687Labels = mixedMoment B raw4687step0 raw4687step0Labels := by
      have hz : ∀ j, raw4687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4687step0 = (fun i j => raw4687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4687step0 raw4687; decide +kernel
      have hl : raw4687step0Labels = raw4687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4687 raw4687Labels permutation346 hz
    mixedMoment B raw4687step0 raw4687step0Labels = mixedMoment B raw4687step1 raw4687step1Labels := by
      have ha : raw4687step1 = (fun i j => raw4687step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4687step1 raw4687step0; decide +kernel
      have hl : raw4687step1Labels = raw4687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4687step0 raw4687step0Labels permutation40 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw4688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4688 raw4688Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw4688 raw4688Labels = mixedMoment B raw4688step0 raw4688step0Labels := by
      have hz : ∀ j, raw4688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4688step0 = (fun i j => raw4688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4688step0 raw4688; decide +kernel
      have hl : raw4688step0Labels = raw4688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4688 raw4688Labels permutation265 hz
    mixedMoment B raw4688step0 raw4688step0Labels = mixedMoment B raw4688step1 raw4688step1Labels := by
      have ha : raw4688step1 = (fun i j => raw4688step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4688step1 raw4688step0; decide +kernel
      have hl : raw4688step1Labels = raw4688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4688step0 raw4688step0Labels permutation40 permutation3
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw4689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4689 raw4689Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw4689 raw4689Labels = mixedMoment B raw4689step0 raw4689step0Labels := by
      have ha : raw4689step0 = (fun i j => raw4689 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4689step0 raw4689; decide +kernel
      have hl : raw4689step0Labels = raw4689Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4689 raw4689Labels permutation160 permutation3
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw4690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4690 raw4690Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw4690 raw4690Labels = mixedMoment B raw4690step0 raw4690step0Labels := by
      have hz : ∀ j, raw4690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4690step0 = (fun i j => raw4690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4690step0 raw4690; decide +kernel
      have hl : raw4690step0Labels = raw4690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4690 raw4690Labels permutation265 hz
    mixedMoment B raw4690step0 raw4690step0Labels = mixedMoment B raw4690step1 raw4690step1Labels := by
      have ha : raw4690step1 = (fun i j => raw4690step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4690step1 raw4690step0; decide +kernel
      have hl : raw4690step1Labels = raw4690step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4690step0 raw4690step0Labels permutation40 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw4691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw4691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4691 raw4691Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw4691 raw4691Labels = mixedMoment B raw4691step0 raw4691step0Labels := by
      have hz : ∀ j, raw4691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4691step0 = (fun i j => raw4691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4691step0 raw4691; decide +kernel
      have hl : raw4691step0Labels = raw4691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4691 raw4691Labels permutation265 hz
    mixedMoment B raw4691step0 raw4691step0Labels = mixedMoment B raw4691step1 raw4691step1Labels := by
      have ha : raw4691step1 = (fun i j => raw4691step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4691step1 raw4691step0; decide +kernel
      have hl : raw4691step1Labels = raw4691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4691step0 raw4691step0Labels permutation46 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw4692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4692 raw4692Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw4692 raw4692Labels = mixedMoment B raw4692step0 raw4692step0Labels := by
      have hz : ∀ j, raw4692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4692step0 = (fun i j => raw4692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4692step0 raw4692; decide +kernel
      have hl : raw4692step0Labels = raw4692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4692 raw4692Labels permutation265 hz
    mixedMoment B raw4692step0 raw4692step0Labels = mixedMoment B raw4692step1 raw4692step1Labels := by
      have ha : raw4692step1 = (fun i j => raw4692step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4692step1 raw4692step0; decide +kernel
      have hl : raw4692step1Labels = raw4692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4692step0 raw4692step0Labels permutation40 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw4693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4693 raw4693Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw4693 raw4693Labels = mixedMoment B raw4693step0 raw4693step0Labels := by
      have hz : ∀ j, raw4693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4693step0 = (fun i j => raw4693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4693step0 raw4693; decide +kernel
      have hl : raw4693step0Labels = raw4693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4693 raw4693Labels permutation346 hz
    mixedMoment B raw4693step0 raw4693step0Labels = mixedMoment B raw4693step1 raw4693step1Labels := by
      have hz : ∀ j, raw4693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4693step1 = (fun i j => raw4693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4693step1 raw4693step0; decide +kernel
      have hl : raw4693step1Labels = raw4693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4693step0 raw4693step0Labels permutation56 hz
    mixedMoment B raw4693step1 raw4693step1Labels = mixedMoment B raw4693step2 raw4693step2Labels := by
      have ha : raw4693step2 = (fun i j => raw4693step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4693step2 raw4693step1; decide +kernel
      have hl : raw4693step2Labels = raw4693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4693step1 raw4693step1Labels permutation10 permutation3
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw4694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4694 raw4694Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw4694 raw4694Labels = mixedMoment B raw4694step0 raw4694step0Labels := by
      have hz : ∀ j, raw4694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4694step0 = (fun i j => raw4694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4694step0 raw4694; decide +kernel
      have hl : raw4694step0Labels = raw4694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4694 raw4694Labels permutation346 hz
    mixedMoment B raw4694step0 raw4694step0Labels = mixedMoment B raw4694step1 raw4694step1Labels := by
      have ha : raw4694step1 = (fun i j => raw4694step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4694step1 raw4694step0; decide +kernel
      have hl : raw4694step1Labels = raw4694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4694step0 raw4694step0Labels permutation34 permutation3
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw4695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4695 raw4695Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw4695 raw4695Labels = mixedMoment B raw4695step0 raw4695step0Labels := by
      have hz : ∀ j, raw4695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4695step0 = (fun i j => raw4695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4695step0 raw4695; decide +kernel
      have hl : raw4695step0Labels = raw4695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4695 raw4695Labels permutation265 hz
    mixedMoment B raw4695step0 raw4695step0Labels = mixedMoment B raw4695step1 raw4695step1Labels := by
      have ha : raw4695step1 = (fun i j => raw4695step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4695step1 raw4695step0; decide +kernel
      have hl : raw4695step1Labels = raw4695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4695step0 raw4695step0Labels permutation34 permutation3
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw4696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4696 raw4696Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw4696 raw4696Labels = mixedMoment B raw4696step0 raw4696step0Labels := by
      have hz : ∀ j, raw4696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4696step0 = (fun i j => raw4696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4696step0 raw4696; decide +kernel
      have hl : raw4696step0Labels = raw4696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4696 raw4696Labels permutation346 hz
    mixedMoment B raw4696step0 raw4696step0Labels = mixedMoment B raw4696step1 raw4696step1Labels := by
      have hz : ∀ j, raw4696step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4696step1 = (fun i j => raw4696step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4696step1 raw4696step0; decide +kernel
      have hl : raw4696step1Labels = raw4696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4696step0 raw4696step0Labels permutation56 hz
    mixedMoment B raw4696step1 raw4696step1Labels = mixedMoment B raw4696step2 raw4696step2Labels := by
      have ha : raw4696step2 = (fun i j => raw4696step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4696step2 raw4696step1; decide +kernel
      have hl : raw4696step2Labels = raw4696step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4696step1 raw4696step1Labels permutation10 permutation3
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw4697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4697 raw4697Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw4697 raw4697Labels = mixedMoment B raw4697step0 raw4697step0Labels := by
      have hz : ∀ j, raw4697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4697step0 = (fun i j => raw4697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4697step0 raw4697; decide +kernel
      have hl : raw4697step0Labels = raw4697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4697 raw4697Labels permutation346 hz
    mixedMoment B raw4697step0 raw4697step0Labels = mixedMoment B raw4697step1 raw4697step1Labels := by
      have hz : ∀ j, raw4697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4697step1 = (fun i j => raw4697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4697step1 raw4697step0; decide +kernel
      have hl : raw4697step1Labels = raw4697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4697step0 raw4697step0Labels permutation56 hz
    mixedMoment B raw4697step1 raw4697step1Labels = mixedMoment B raw4697step2 raw4697step2Labels := by
      have ha : raw4697step2 = (fun i j => raw4697step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4697step2 raw4697step1; decide +kernel
      have hl : raw4697step2Labels = raw4697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4697step1 raw4697step1Labels permutation10 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw4698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4698 raw4698Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw4698 raw4698Labels = mixedMoment B raw4698step0 raw4698step0Labels := by
      have hz : ∀ j, raw4698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4698step0 = (fun i j => raw4698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4698step0 raw4698; decide +kernel
      have hl : raw4698step0Labels = raw4698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4698 raw4698Labels permutation346 hz
    mixedMoment B raw4698step0 raw4698step0Labels = mixedMoment B raw4698step1 raw4698step1Labels := by
      have hz : ∀ j, raw4698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4698step1 = (fun i j => raw4698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4698step1 raw4698step0; decide +kernel
      have hl : raw4698step1Labels = raw4698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4698step0 raw4698step0Labels permutation56 hz
    mixedMoment B raw4698step1 raw4698step1Labels = mixedMoment B raw4698step2 raw4698step2Labels := by
      have ha : raw4698step2 = (fun i j => raw4698step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4698step2 raw4698step1; decide +kernel
      have hl : raw4698step2Labels = raw4698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4698step1 raw4698step1Labels permutation8 permutation3
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw4699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4699 raw4699Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw4699 raw4699Labels = mixedMoment B raw4699step0 raw4699step0Labels := by
      have hz : ∀ j, raw4699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4699step0 = (fun i j => raw4699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4699step0 raw4699; decide +kernel
      have hl : raw4699step0Labels = raw4699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4699 raw4699Labels permutation346 hz
    mixedMoment B raw4699step0 raw4699step0Labels = mixedMoment B raw4699step1 raw4699step1Labels := by
      have ha : raw4699step1 = (fun i j => raw4699step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4699step1 raw4699step0; decide +kernel
      have hl : raw4699step1Labels = raw4699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4699step0 raw4699step0Labels permutation32 permutation3
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw4700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw4700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4700 raw4700Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw4700 raw4700Labels = mixedMoment B raw4700step0 raw4700step0Labels := by
      have hz : ∀ j, raw4700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4700step0 = (fun i j => raw4700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4700step0 raw4700; decide +kernel
      have hl : raw4700step0Labels = raw4700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4700 raw4700Labels permutation265 hz
    mixedMoment B raw4700step0 raw4700step0Labels = mixedMoment B raw4700step1 raw4700step1Labels := by
      have ha : raw4700step1 = (fun i j => raw4700step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4700step1 raw4700step0; decide +kernel
      have hl : raw4700step1Labels = raw4700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4700step0 raw4700step0Labels permutation32 permutation3
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw4701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw4701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4701 raw4701Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw4701 raw4701Labels = mixedMoment B raw4701step0 raw4701step0Labels := by
      have hz : ∀ j, raw4701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4701step0 = (fun i j => raw4701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4701step0 raw4701; decide +kernel
      have hl : raw4701step0Labels = raw4701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4701 raw4701Labels permutation346 hz
    mixedMoment B raw4701step0 raw4701step0Labels = mixedMoment B raw4701step1 raw4701step1Labels := by
      have hz : ∀ j, raw4701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4701step1 = (fun i j => raw4701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4701step1 raw4701step0; decide +kernel
      have hl : raw4701step1Labels = raw4701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4701step0 raw4701step0Labels permutation56 hz
    mixedMoment B raw4701step1 raw4701step1Labels = mixedMoment B raw4701step2 raw4701step2Labels := by
      have ha : raw4701step2 = (fun i j => raw4701step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4701step2 raw4701step1; decide +kernel
      have hl : raw4701step2Labels = raw4701step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4701step1 raw4701step1Labels permutation8 permutation3
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw4702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4702step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw4702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4702 raw4702Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw4702 raw4702Labels = mixedMoment B raw4702step0 raw4702step0Labels := by
      have hz : ∀ j, raw4702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4702step0 = (fun i j => raw4702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4702step0 raw4702; decide +kernel
      have hl : raw4702step0Labels = raw4702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4702 raw4702Labels permutation346 hz
    mixedMoment B raw4702step0 raw4702step0Labels = mixedMoment B raw4702step1 raw4702step1Labels := by
      have hz : ∀ j, raw4702step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4702step1 = (fun i j => raw4702step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4702step1 raw4702step0; decide +kernel
      have hl : raw4702step1Labels = raw4702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4702step0 raw4702step0Labels permutation56 hz
    mixedMoment B raw4702step1 raw4702step1Labels = mixedMoment B raw4702step2 raw4702step2Labels := by
      have ha : raw4702step2 = (fun i j => raw4702step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4702step2 raw4702step1; decide +kernel
      have hl : raw4702step2Labels = raw4702step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4702step1 raw4702step1Labels permutation8 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw4703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4703step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4703 raw4703Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw4703 raw4703Labels = mixedMoment B raw4703step0 raw4703step0Labels := by
      have hz : ∀ j, raw4703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4703step0 = (fun i j => raw4703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4703step0 raw4703; decide +kernel
      have hl : raw4703step0Labels = raw4703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4703 raw4703Labels permutation346 hz
    mixedMoment B raw4703step0 raw4703step0Labels = mixedMoment B raw4703step1 raw4703step1Labels := by
      have hz : ∀ j, raw4703step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4703step1 = (fun i j => raw4703step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4703step1 raw4703step0; decide +kernel
      have hl : raw4703step1Labels = raw4703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4703step0 raw4703step0Labels permutation56 hz
    mixedMoment B raw4703step1 raw4703step1Labels = mixedMoment B raw4703step2 raw4703step2Labels := by
      have ha : raw4703step2 = (fun i j => raw4703step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4703step2 raw4703step1; decide +kernel
      have hl : raw4703step2Labels = raw4703step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4703step1 raw4703step1Labels permutation8 permutation3
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw4704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4704 raw4704Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw4704 raw4704Labels = mixedMoment B raw4704step0 raw4704step0Labels := by
      have hz : ∀ j, raw4704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4704step0 = (fun i j => raw4704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4704step0 raw4704; decide +kernel
      have hl : raw4704step0Labels = raw4704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4704 raw4704Labels permutation346 hz
    mixedMoment B raw4704step0 raw4704step0Labels = mixedMoment B raw4704step1 raw4704step1Labels := by
      have ha : raw4704step1 = (fun i j => raw4704step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4704step1 raw4704step0; decide +kernel
      have hl : raw4704step1Labels = raw4704step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4704step0 raw4704step0Labels permutation145 permutation3
    mixedMoment B raw4704step1 raw4704step1Labels = mixedMoment B raw4704step2 raw4704step2Labels := by
      have ha : raw4704step2 = -raw4704step1 := by apply Matrix.ext; change ∀ i j, raw4704step2 i j = -(raw4704step1 i j); unfold raw4704step2 raw4704step1; decide +kernel
      have hl : raw4704step2Labels = raw4704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw4705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4705 raw4705Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw4705 raw4705Labels = mixedMoment B raw4705step0 raw4705step0Labels := by
      have hz : ∀ j, raw4705 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4705step0 = (fun i j => raw4705 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4705step0 raw4705; decide +kernel
      have hl : raw4705step0Labels = raw4705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4705 raw4705Labels permutation265 hz
    mixedMoment B raw4705step0 raw4705step0Labels = mixedMoment B raw4705step1 raw4705step1Labels := by
      have ha : raw4705step1 = (fun i j => raw4705step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4705step1 raw4705step0; decide +kernel
      have hl : raw4705step1Labels = raw4705step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4705step0 raw4705step0Labels permutation145 permutation3
    mixedMoment B raw4705step1 raw4705step1Labels = mixedMoment B raw4705step2 raw4705step2Labels := by
      have ha : raw4705step2 = -raw4705step1 := by apply Matrix.ext; change ∀ i j, raw4705step2 i j = -(raw4705step1 i j); unfold raw4705step2 raw4705step1; decide +kernel
      have hl : raw4705step2Labels = raw4705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw4706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4706step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw4706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4706 raw4706Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw4706 raw4706Labels = mixedMoment B raw4706step0 raw4706step0Labels := by
      have hz : ∀ j, raw4706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4706step0 = (fun i j => raw4706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4706step0 raw4706; decide +kernel
      have hl : raw4706step0Labels = raw4706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4706 raw4706Labels permutation346 hz
    mixedMoment B raw4706step0 raw4706step0Labels = mixedMoment B raw4706step1 raw4706step1Labels := by
      have hz : ∀ j, raw4706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4706step1 = (fun i j => raw4706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4706step1 raw4706step0; decide +kernel
      have hl : raw4706step1Labels = raw4706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4706step0 raw4706step0Labels permutation56 hz
    mixedMoment B raw4706step1 raw4706step1Labels = mixedMoment B raw4706step2 raw4706step2Labels := by
      have ha : raw4706step2 = (fun i j => raw4706step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4706step2 raw4706step1; decide +kernel
      have hl : raw4706step2Labels = raw4706step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4706step1 raw4706step1Labels permutation31 permutation3
    mixedMoment B raw4706step2 raw4706step2Labels = mixedMoment B raw4706step3 raw4706step3Labels := by
      have ha : raw4706step3 = -raw4706step2 := by apply Matrix.ext; change ∀ i j, raw4706step3 i j = -(raw4706step2 i j); unfold raw4706step3 raw4706step2; decide +kernel
      have hl : raw4706step3Labels = raw4706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw4707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw4707step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw4707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4707 raw4707Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw4707 raw4707Labels = mixedMoment B raw4707step0 raw4707step0Labels := by
      have hz : ∀ j, raw4707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4707step0 = (fun i j => raw4707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4707step0 raw4707; decide +kernel
      have hl : raw4707step0Labels = raw4707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4707 raw4707Labels permutation346 hz
    mixedMoment B raw4707step0 raw4707step0Labels = mixedMoment B raw4707step1 raw4707step1Labels := by
      have hz : ∀ j, raw4707step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4707step1 = (fun i j => raw4707step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4707step1 raw4707step0; decide +kernel
      have hl : raw4707step1Labels = raw4707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4707step0 raw4707step0Labels permutation56 hz
    mixedMoment B raw4707step1 raw4707step1Labels = mixedMoment B raw4707step2 raw4707step2Labels := by
      have ha : raw4707step2 = (fun i j => raw4707step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4707step2 raw4707step1; decide +kernel
      have hl : raw4707step2Labels = raw4707step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4707step1 raw4707step1Labels permutation29 permutation3
    mixedMoment B raw4707step2 raw4707step2Labels = mixedMoment B raw4707step3 raw4707step3Labels := by
      have ha : raw4707step3 = -raw4707step2 := by apply Matrix.ext; change ∀ i j, raw4707step3 i j = -(raw4707step2 i j); unfold raw4707step3 raw4707step2; decide +kernel
      have hl : raw4707step3Labels = raw4707step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw4708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4708 raw4708Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw4708 raw4708Labels = mixedMoment B raw4708step0 raw4708step0Labels := by
      have hz : ∀ j, raw4708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4708step0 = (fun i j => raw4708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4708step0 raw4708; decide +kernel
      have hl : raw4708step0Labels = raw4708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4708 raw4708Labels permutation346 hz
    mixedMoment B raw4708step0 raw4708step0Labels = mixedMoment B raw4708step1 raw4708step1Labels := by
      have ha : raw4708step1 = (fun i j => raw4708step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4708step1 raw4708step0; decide +kernel
      have hl : raw4708step1Labels = raw4708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4708step0 raw4708step0Labels permutation137 permutation7
    mixedMoment B raw4708step1 raw4708step1Labels = mixedMoment B raw4708step2 raw4708step2Labels := by
      have ha : raw4708step2 = raw4708step1 := by apply Matrix.ext; unfold raw4708step2 raw4708step1; decide +kernel
      have hl : raw4708step1Labels = labelEmbedding1 ∘ raw4708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4708step1 raw4708step1Labels raw4708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw4709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4709 raw4709Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw4709 raw4709Labels = mixedMoment B raw4709step0 raw4709step0Labels := by
      have hz : ∀ j, raw4709 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4709step0 = (fun i j => raw4709 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4709step0 raw4709; decide +kernel
      have hl : raw4709step0Labels = raw4709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4709 raw4709Labels permutation265 hz
    mixedMoment B raw4709step0 raw4709step0Labels = mixedMoment B raw4709step1 raw4709step1Labels := by
      have ha : raw4709step1 = (fun i j => raw4709step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4709step1 raw4709step0; decide +kernel
      have hl : raw4709step1Labels = raw4709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4709step0 raw4709step0Labels permutation137 permutation7
    mixedMoment B raw4709step1 raw4709step1Labels = mixedMoment B raw4709step2 raw4709step2Labels := by
      have ha : raw4709step2 = raw4709step1 := by apply Matrix.ext; unfold raw4709step2 raw4709step1; decide +kernel
      have hl : raw4709step1Labels = labelEmbedding1 ∘ raw4709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4709step1 raw4709step1Labels raw4709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw4710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4710step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4710 raw4710Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw4710 raw4710Labels = mixedMoment B raw4710step0 raw4710step0Labels := by
      have hz : ∀ j, raw4710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4710step0 = (fun i j => raw4710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4710step0 raw4710; decide +kernel
      have hl : raw4710step0Labels = raw4710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4710 raw4710Labels permutation346 hz
    mixedMoment B raw4710step0 raw4710step0Labels = mixedMoment B raw4710step1 raw4710step1Labels := by
      have hz : ∀ j, raw4710step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4710step1 = (fun i j => raw4710step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4710step1 raw4710step0; decide +kernel
      have hl : raw4710step1Labels = raw4710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4710step0 raw4710step0Labels permutation56 hz
    mixedMoment B raw4710step1 raw4710step1Labels = mixedMoment B raw4710step2 raw4710step2Labels := by
      have ha : raw4710step2 = (fun i j => raw4710step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4710step2 raw4710step1; decide +kernel
      have hl : raw4710step2Labels = raw4710step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4710step1 raw4710step1Labels permutation31 permutation7
    mixedMoment B raw4710step2 raw4710step2Labels = mixedMoment B raw4710step3 raw4710step3Labels := by
      have ha : raw4710step3 = raw4710step2 := by apply Matrix.ext; unfold raw4710step3 raw4710step2; decide +kernel
      have hl : raw4710step2Labels = labelEmbedding1 ∘ raw4710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4710step2 raw4710step2Labels raw4710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw4711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4711 raw4711Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw4711 raw4711Labels = mixedMoment B raw4711step0 raw4711step0Labels := by
      have hz : ∀ j, raw4711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4711step0 = (fun i j => raw4711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4711step0 raw4711; decide +kernel
      have hl : raw4711step0Labels = raw4711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4711 raw4711Labels permutation346 hz
    mixedMoment B raw4711step0 raw4711step0Labels = mixedMoment B raw4711step1 raw4711step1Labels := by
      have hz : ∀ j, raw4711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4711step1 = (fun i j => raw4711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4711step1 raw4711step0; decide +kernel
      have hl : raw4711step1Labels = raw4711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4711step0 raw4711step0Labels permutation56 hz
    mixedMoment B raw4711step1 raw4711step1Labels = mixedMoment B raw4711step2 raw4711step2Labels := by
      have ha : raw4711step2 = (fun i j => raw4711step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4711step2 raw4711step1; decide +kernel
      have hl : raw4711step2Labels = raw4711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4711step1 raw4711step1Labels permutation29 permutation7
    mixedMoment B raw4711step2 raw4711step2Labels = mixedMoment B raw4711step3 raw4711step3Labels := by
      have ha : raw4711step3 = raw4711step2 := by apply Matrix.ext; unfold raw4711step3 raw4711step2; decide +kernel
      have hl : raw4711step2Labels = labelEmbedding1 ∘ raw4711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4711step2 raw4711step2Labels raw4711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw4712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4712 raw4712Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw4712 raw4712Labels = mixedMoment B raw4712step0 raw4712step0Labels := by
      have hz : ∀ j, raw4712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4712step0 = (fun i j => raw4712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4712step0 raw4712; decide +kernel
      have hl : raw4712step0Labels = raw4712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4712 raw4712Labels permutation346 hz
    mixedMoment B raw4712step0 raw4712step0Labels = mixedMoment B raw4712step1 raw4712step1Labels := by
      have hz : ∀ j, raw4712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4712step1 = (fun i j => raw4712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4712step1 raw4712step0; decide +kernel
      have hl : raw4712step1Labels = raw4712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4712step0 raw4712step0Labels permutation56 hz
    mixedMoment B raw4712step1 raw4712step1Labels = mixedMoment B raw4712step2 raw4712step2Labels := by
      have ha : raw4712step2 = (fun i j => raw4712step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4712step2 raw4712step1; decide +kernel
      have hl : raw4712step2Labels = raw4712step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4712step1 raw4712step1Labels permutation29 permutation7
    mixedMoment B raw4712step2 raw4712step2Labels = mixedMoment B raw4712step3 raw4712step3Labels := by
      have ha : raw4712step3 = raw4712step2 := by apply Matrix.ext; unfold raw4712step3 raw4712step2; decide +kernel
      have hl : raw4712step2Labels = labelEmbedding1 ∘ raw4712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4712step2 raw4712step2Labels raw4712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw4713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw4713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4713 raw4713Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw4713 raw4713Labels = mixedMoment B raw4713step0 raw4713step0Labels := by
      have hz : ∀ j, raw4713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4713step0 = (fun i j => raw4713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4713step0 raw4713; decide +kernel
      have hl : raw4713step0Labels = raw4713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4713 raw4713Labels permutation346 hz
    mixedMoment B raw4713step0 raw4713step0Labels = mixedMoment B raw4713step1 raw4713step1Labels := by
      have ha : raw4713step1 = (fun i j => raw4713step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4713step1 raw4713step0; decide +kernel
      have hl : raw4713step1Labels = raw4713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4713step0 raw4713step0Labels permutation53 permutation5
    mixedMoment B raw4713step1 raw4713step1Labels = mixedMoment B raw4713step2 raw4713step2Labels := by
      have ha : raw4713step2 = -raw4713step1 := by apply Matrix.ext; change ∀ i j, raw4713step2 i j = -(raw4713step1 i j); unfold raw4713step2 raw4713step1; decide +kernel
      have hl : raw4713step2Labels = raw4713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4713step2 raw4713step2Labels = mixedMoment B raw4713step3 raw4713step3Labels := by
      have ha : raw4713step3 = raw4713step2 := by apply Matrix.ext; unfold raw4713step3 raw4713step2; decide +kernel
      have hl : raw4713step2Labels = labelEmbedding1 ∘ raw4713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4713step2 raw4713step2Labels raw4713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw4714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4714 raw4714Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw4714 raw4714Labels = mixedMoment B raw4714step0 raw4714step0Labels := by
      have ha : raw4714step0 = (fun i j => raw4714 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4714step0 raw4714; decide +kernel
      have hl : raw4714step0Labels = raw4714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4714 raw4714Labels permutation609 permutation7
    mixedMoment B raw4714step0 raw4714step0Labels = mixedMoment B raw4714step1 raw4714step1Labels := by
      have ha : raw4714step1 = raw4714step0 := by apply Matrix.ext; unfold raw4714step1 raw4714step0; decide +kernel
      have hl : raw4714step0Labels = labelEmbedding1 ∘ raw4714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4714step0 raw4714step0Labels raw4714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw4715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4715 raw4715Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4715 raw4715Labels = mixedMoment B raw4715step0 raw4715step0Labels := by
      have hz : ∀ j, raw4715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4715step0 = (fun i j => raw4715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4715step0 raw4715; decide +kernel
      have hl : raw4715step0Labels = raw4715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4715 raw4715Labels permutation346 hz
    mixedMoment B raw4715step0 raw4715step0Labels = mixedMoment B raw4715step1 raw4715step1Labels := by
      have ha : raw4715step1 = (fun i j => raw4715step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4715step1 raw4715step0; decide +kernel
      have hl : raw4715step1Labels = raw4715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4715step0 raw4715step0Labels permutation139 permutation7
    mixedMoment B raw4715step1 raw4715step1Labels = mixedMoment B raw4715step2 raw4715step2Labels := by
      have ha : raw4715step2 = raw4715step1 := by apply Matrix.ext; unfold raw4715step2 raw4715step1; decide +kernel
      have hl : raw4715step1Labels = labelEmbedding1 ∘ raw4715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4715step1 raw4715step1Labels raw4715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw4716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4716 raw4716Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4716 raw4716Labels = mixedMoment B raw4716step0 raw4716step0Labels := by
      have hz : ∀ j, raw4716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4716step0 = (fun i j => raw4716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4716step0 raw4716; decide +kernel
      have hl : raw4716step0Labels = raw4716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4716 raw4716Labels permutation346 hz
    mixedMoment B raw4716step0 raw4716step0Labels = mixedMoment B raw4716step1 raw4716step1Labels := by
      have ha : raw4716step1 = (fun i j => raw4716step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4716step1 raw4716step0; decide +kernel
      have hl : raw4716step1Labels = raw4716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4716step0 raw4716step0Labels permutation137 permutation7
    mixedMoment B raw4716step1 raw4716step1Labels = mixedMoment B raw4716step2 raw4716step2Labels := by
      have ha : raw4716step2 = raw4716step1 := by apply Matrix.ext; unfold raw4716step2 raw4716step1; decide +kernel
      have hl : raw4716step1Labels = labelEmbedding1 ∘ raw4716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4716step1 raw4716step1Labels raw4716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw4717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4717 raw4717Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw4717 raw4717Labels = mixedMoment B raw4717step0 raw4717step0Labels := by
      have hz : ∀ j, raw4717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4717step0 = (fun i j => raw4717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4717step0 raw4717; decide +kernel
      have hl : raw4717step0Labels = raw4717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4717 raw4717Labels permutation346 hz
    mixedMoment B raw4717step0 raw4717step0Labels = mixedMoment B raw4717step1 raw4717step1Labels := by
      have ha : raw4717step1 = (fun i j => raw4717step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4717step1 raw4717step0; decide +kernel
      have hl : raw4717step1Labels = raw4717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4717step0 raw4717step0Labels permutation137 permutation7
    mixedMoment B raw4717step1 raw4717step1Labels = mixedMoment B raw4717step2 raw4717step2Labels := by
      have ha : raw4717step2 = raw4717step1 := by apply Matrix.ext; unfold raw4717step2 raw4717step1; decide +kernel
      have hl : raw4717step1Labels = labelEmbedding1 ∘ raw4717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4717step1 raw4717step1Labels raw4717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw4718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw4718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4718 raw4718Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw4718 raw4718Labels = mixedMoment B raw4718step0 raw4718step0Labels := by
      have hz : ∀ j, raw4718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4718step0 = (fun i j => raw4718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4718step0 raw4718; decide +kernel
      have hl : raw4718step0Labels = raw4718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4718 raw4718Labels permutation265 hz
    mixedMoment B raw4718step0 raw4718step0Labels = mixedMoment B raw4718step1 raw4718step1Labels := by
      have ha : raw4718step1 = (fun i j => raw4718step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4718step1 raw4718step0; decide +kernel
      have hl : raw4718step1Labels = raw4718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4718step0 raw4718step0Labels permutation53 permutation5
    mixedMoment B raw4718step1 raw4718step1Labels = mixedMoment B raw4718step2 raw4718step2Labels := by
      have ha : raw4718step2 = -raw4718step1 := by apply Matrix.ext; change ∀ i j, raw4718step2 i j = -(raw4718step1 i j); unfold raw4718step2 raw4718step1; decide +kernel
      have hl : raw4718step2Labels = raw4718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4718step2 raw4718step2Labels = mixedMoment B raw4718step3 raw4718step3Labels := by
      have ha : raw4718step3 = raw4718step2 := by apply Matrix.ext; unfold raw4718step3 raw4718step2; decide +kernel
      have hl : raw4718step2Labels = labelEmbedding1 ∘ raw4718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4718step2 raw4718step2Labels raw4718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw4719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4719 raw4719Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw4719 raw4719Labels = mixedMoment B raw4719step0 raw4719step0Labels := by
      have ha : raw4719step0 = (fun i j => raw4719 (permutation632 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4719step0 raw4719; decide +kernel
      have hl : raw4719step0Labels = raw4719Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4719 raw4719Labels permutation632 permutation7
    mixedMoment B raw4719step0 raw4719step0Labels = mixedMoment B raw4719step1 raw4719step1Labels := by
      have ha : raw4719step1 = raw4719step0 := by apply Matrix.ext; unfold raw4719step1 raw4719step0; decide +kernel
      have hl : raw4719step0Labels = labelEmbedding1 ∘ raw4719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4719step0 raw4719step0Labels raw4719step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw4720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4720 raw4720Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4720 raw4720Labels = mixedMoment B raw4720step0 raw4720step0Labels := by
      have hz : ∀ j, raw4720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4720step0 = (fun i j => raw4720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4720step0 raw4720; decide +kernel
      have hl : raw4720step0Labels = raw4720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4720 raw4720Labels permutation265 hz
    mixedMoment B raw4720step0 raw4720step0Labels = mixedMoment B raw4720step1 raw4720step1Labels := by
      have ha : raw4720step1 = (fun i j => raw4720step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4720step1 raw4720step0; decide +kernel
      have hl : raw4720step1Labels = raw4720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4720step0 raw4720step0Labels permutation139 permutation7
    mixedMoment B raw4720step1 raw4720step1Labels = mixedMoment B raw4720step2 raw4720step2Labels := by
      have ha : raw4720step2 = raw4720step1 := by apply Matrix.ext; unfold raw4720step2 raw4720step1; decide +kernel
      have hl : raw4720step1Labels = labelEmbedding1 ∘ raw4720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4720step1 raw4720step1Labels raw4720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw4721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4721 raw4721Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw4721 raw4721Labels = mixedMoment B raw4721step0 raw4721step0Labels := by
      have hz : ∀ j, raw4721 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4721step0 = (fun i j => raw4721 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4721step0 raw4721; decide +kernel
      have hl : raw4721step0Labels = raw4721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4721 raw4721Labels permutation265 hz
    mixedMoment B raw4721step0 raw4721step0Labels = mixedMoment B raw4721step1 raw4721step1Labels := by
      have ha : raw4721step1 = (fun i j => raw4721step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4721step1 raw4721step0; decide +kernel
      have hl : raw4721step1Labels = raw4721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4721step0 raw4721step0Labels permutation137 permutation7
    mixedMoment B raw4721step1 raw4721step1Labels = mixedMoment B raw4721step2 raw4721step2Labels := by
      have ha : raw4721step2 = raw4721step1 := by apply Matrix.ext; unfold raw4721step2 raw4721step1; decide +kernel
      have hl : raw4721step1Labels = labelEmbedding1 ∘ raw4721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4721step1 raw4721step1Labels raw4721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw4722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4722 raw4722Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw4722 raw4722Labels = mixedMoment B raw4722step0 raw4722step0Labels := by
      have hz : ∀ j, raw4722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4722step0 = (fun i j => raw4722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4722step0 raw4722; decide +kernel
      have hl : raw4722step0Labels = raw4722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4722 raw4722Labels permutation265 hz
    mixedMoment B raw4722step0 raw4722step0Labels = mixedMoment B raw4722step1 raw4722step1Labels := by
      have ha : raw4722step1 = (fun i j => raw4722step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4722step1 raw4722step0; decide +kernel
      have hl : raw4722step1Labels = raw4722step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4722step0 raw4722step0Labels permutation137 permutation7
    mixedMoment B raw4722step1 raw4722step1Labels = mixedMoment B raw4722step2 raw4722step2Labels := by
      have ha : raw4722step2 = raw4722step1 := by apply Matrix.ext; unfold raw4722step2 raw4722step1; decide +kernel
      have hl : raw4722step1Labels = labelEmbedding1 ∘ raw4722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4722step1 raw4722step1Labels raw4722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw4723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4723 raw4723Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw4723 raw4723Labels = mixedMoment B raw4723step0 raw4723step0Labels := by
      have hz : ∀ j, raw4723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4723step0 = (fun i j => raw4723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4723step0 raw4723; decide +kernel
      have hl : raw4723step0Labels = raw4723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4723 raw4723Labels permutation346 hz
    mixedMoment B raw4723step0 raw4723step0Labels = mixedMoment B raw4723step1 raw4723step1Labels := by
      have hz : ∀ j, raw4723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4723step1 = (fun i j => raw4723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4723step1 raw4723step0; decide +kernel
      have hl : raw4723step1Labels = raw4723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4723step0 raw4723step0Labels permutation56 hz
    mixedMoment B raw4723step1 raw4723step1Labels = mixedMoment B raw4723step2 raw4723step2Labels := by
      have ha : raw4723step2 = (fun i j => raw4723step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4723step2 raw4723step1; decide +kernel
      have hl : raw4723step2Labels = raw4723step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4723step1 raw4723step1Labels permutation13 permutation5
    mixedMoment B raw4723step2 raw4723step2Labels = mixedMoment B raw4723step3 raw4723step3Labels := by
      have ha : raw4723step3 = -raw4723step2 := by apply Matrix.ext; change ∀ i j, raw4723step3 i j = -(raw4723step2 i j); unfold raw4723step3 raw4723step2; decide +kernel
      have hl : raw4723step3Labels = raw4723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4723step3 raw4723step3Labels = mixedMoment B raw4723step4 raw4723step4Labels := by
      have ha : raw4723step4 = raw4723step3 := by apply Matrix.ext; unfold raw4723step4 raw4723step3; decide +kernel
      have hl : raw4723step3Labels = labelEmbedding1 ∘ raw4723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4723step3 raw4723step3Labels raw4723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw4724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4724 raw4724Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4724 raw4724Labels = mixedMoment B raw4724step0 raw4724step0Labels := by
      have hz : ∀ j, raw4724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4724step0 = (fun i j => raw4724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4724step0 raw4724; decide +kernel
      have hl : raw4724step0Labels = raw4724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4724 raw4724Labels permutation346 hz
    mixedMoment B raw4724step0 raw4724step0Labels = mixedMoment B raw4724step1 raw4724step1Labels := by
      have ha : raw4724step1 = (fun i j => raw4724step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4724step1 raw4724step0; decide +kernel
      have hl : raw4724step1Labels = raw4724step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4724step0 raw4724step0Labels permutation137 permutation7
    mixedMoment B raw4724step1 raw4724step1Labels = mixedMoment B raw4724step2 raw4724step2Labels := by
      have ha : raw4724step2 = raw4724step1 := by apply Matrix.ext; unfold raw4724step2 raw4724step1; decide +kernel
      have hl : raw4724step1Labels = labelEmbedding1 ∘ raw4724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4724step1 raw4724step1Labels raw4724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw4725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw4725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4725 raw4725Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4725 raw4725Labels = mixedMoment B raw4725step0 raw4725step0Labels := by
      have hz : ∀ j, raw4725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4725step0 = (fun i j => raw4725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4725step0 raw4725; decide +kernel
      have hl : raw4725step0Labels = raw4725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4725 raw4725Labels permutation265 hz
    mixedMoment B raw4725step0 raw4725step0Labels = mixedMoment B raw4725step1 raw4725step1Labels := by
      have ha : raw4725step1 = (fun i j => raw4725step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4725step1 raw4725step0; decide +kernel
      have hl : raw4725step1Labels = raw4725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4725step0 raw4725step0Labels permutation137 permutation7
    mixedMoment B raw4725step1 raw4725step1Labels = mixedMoment B raw4725step2 raw4725step2Labels := by
      have ha : raw4725step2 = raw4725step1 := by apply Matrix.ext; unfold raw4725step2 raw4725step1; decide +kernel
      have hl : raw4725step1Labels = labelEmbedding1 ∘ raw4725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4725step1 raw4725step1Labels raw4725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw4726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![3, 0, -3]]
def raw4726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4726 raw4726Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw4726 raw4726Labels = mixedMoment B raw4726step0 raw4726step0Labels := by
      have hz : ∀ j, raw4726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4726step0 = (fun i j => raw4726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4726step0 raw4726; decide +kernel
      have hl : raw4726step0Labels = raw4726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4726 raw4726Labels permutation346 hz
    mixedMoment B raw4726step0 raw4726step0Labels = mixedMoment B raw4726step1 raw4726step1Labels := by
      have hz : ∀ j, raw4726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4726step1 = (fun i j => raw4726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4726step1 raw4726step0; decide +kernel
      have hl : raw4726step1Labels = raw4726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4726step0 raw4726step0Labels permutation56 hz
    mixedMoment B raw4726step1 raw4726step1Labels = mixedMoment B raw4726step2 raw4726step2Labels := by
      have ha : raw4726step2 = (fun i j => raw4726step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4726step2 raw4726step1; decide +kernel
      have hl : raw4726step2Labels = raw4726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4726step1 raw4726step1Labels permutation29 permutation7
    mixedMoment B raw4726step2 raw4726step2Labels = mixedMoment B raw4726step3 raw4726step3Labels := by
      have ha : raw4726step3 = raw4726step2 := by apply Matrix.ext; unfold raw4726step3 raw4726step2; decide +kernel
      have hl : raw4726step2Labels = labelEmbedding1 ∘ raw4726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4726step2 raw4726step2Labels raw4726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw4727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw4727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4727 raw4727Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw4727 raw4727Labels = mixedMoment B raw4727step0 raw4727step0Labels := by
      have hz : ∀ j, raw4727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4727step0 = (fun i j => raw4727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4727step0 raw4727; decide +kernel
      have hl : raw4727step0Labels = raw4727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4727 raw4727Labels permutation346 hz
    mixedMoment B raw4727step0 raw4727step0Labels = mixedMoment B raw4727step1 raw4727step1Labels := by
      have hz : ∀ j, raw4727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4727step1 = (fun i j => raw4727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4727step1 raw4727step0; decide +kernel
      have hl : raw4727step1Labels = raw4727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4727step0 raw4727step0Labels permutation56 hz
    mixedMoment B raw4727step1 raw4727step1Labels = mixedMoment B raw4727step2 raw4727step2Labels := by
      have ha : raw4727step2 = (fun i j => raw4727step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4727step2 raw4727step1; decide +kernel
      have hl : raw4727step2Labels = raw4727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4727step1 raw4727step1Labels permutation29 permutation7
    mixedMoment B raw4727step2 raw4727step2Labels = mixedMoment B raw4727step3 raw4727step3Labels := by
      have ha : raw4727step3 = raw4727step2 := by apply Matrix.ext; unfold raw4727step3 raw4727step2; decide +kernel
      have hl : raw4727step2Labels = labelEmbedding1 ∘ raw4727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4727step2 raw4727step2Labels raw4727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw4728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw4728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw4728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4728 raw4728Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw4728 raw4728Labels = mixedMoment B raw4728step0 raw4728step0Labels := by
      have hz : ∀ j, raw4728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4728step0 = (fun i j => raw4728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4728step0 raw4728; decide +kernel
      have hl : raw4728step0Labels = raw4728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4728 raw4728Labels permutation346 hz
    mixedMoment B raw4728step0 raw4728step0Labels = mixedMoment B raw4728step1 raw4728step1Labels := by
      have hz : ∀ j, raw4728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4728step1 = (fun i j => raw4728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4728step1 raw4728step0; decide +kernel
      have hl : raw4728step1Labels = raw4728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4728step0 raw4728step0Labels permutation56 hz
    mixedMoment B raw4728step1 raw4728step1Labels = mixedMoment B raw4728step2 raw4728step2Labels := by
      have ha : raw4728step2 = (fun i j => raw4728step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4728step2 raw4728step1; decide +kernel
      have hl : raw4728step2Labels = raw4728step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4728step1 raw4728step1Labels permutation12 permutation5
    mixedMoment B raw4728step2 raw4728step2Labels = mixedMoment B raw4728step3 raw4728step3Labels := by
      have ha : raw4728step3 = -raw4728step2 := by apply Matrix.ext; change ∀ i j, raw4728step3 i j = -(raw4728step2 i j); unfold raw4728step3 raw4728step2; decide +kernel
      have hl : raw4728step3Labels = raw4728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4728step3 raw4728step3Labels = mixedMoment B raw4728step4 raw4728step4Labels := by
      have ha : raw4728step4 = raw4728step3 := by apply Matrix.ext; unfold raw4728step4 raw4728step3; decide +kernel
      have hl : raw4728step3Labels = labelEmbedding1 ∘ raw4728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4728step3 raw4728step3Labels raw4728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw4729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4729 raw4729Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4729 raw4729Labels = mixedMoment B raw4729step0 raw4729step0Labels := by
      have hz : ∀ j, raw4729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4729step0 = (fun i j => raw4729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4729step0 raw4729; decide +kernel
      have hl : raw4729step0Labels = raw4729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4729 raw4729Labels permutation346 hz
    mixedMoment B raw4729step0 raw4729step0Labels = mixedMoment B raw4729step1 raw4729step1Labels := by
      have ha : raw4729step1 = (fun i j => raw4729step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4729step1 raw4729step0; decide +kernel
      have hl : raw4729step1Labels = raw4729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4729step0 raw4729step0Labels permutation139 permutation7
    mixedMoment B raw4729step1 raw4729step1Labels = mixedMoment B raw4729step2 raw4729step2Labels := by
      have ha : raw4729step2 = raw4729step1 := by apply Matrix.ext; unfold raw4729step2 raw4729step1; decide +kernel
      have hl : raw4729step1Labels = labelEmbedding1 ∘ raw4729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4729step1 raw4729step1Labels raw4729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw4730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4730 raw4730Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw4730 raw4730Labels = mixedMoment B raw4730step0 raw4730step0Labels := by
      have hz : ∀ j, raw4730 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4730step0 = (fun i j => raw4730 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4730step0 raw4730; decide +kernel
      have hl : raw4730step0Labels = raw4730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4730 raw4730Labels permutation265 hz
    mixedMoment B raw4730step0 raw4730step0Labels = mixedMoment B raw4730step1 raw4730step1Labels := by
      have ha : raw4730step1 = (fun i j => raw4730step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4730step1 raw4730step0; decide +kernel
      have hl : raw4730step1Labels = raw4730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4730step0 raw4730step0Labels permutation139 permutation7
    mixedMoment B raw4730step1 raw4730step1Labels = mixedMoment B raw4730step2 raw4730step2Labels := by
      have ha : raw4730step2 = raw4730step1 := by apply Matrix.ext; unfold raw4730step2 raw4730step1; decide +kernel
      have hl : raw4730step1Labels = labelEmbedding1 ∘ raw4730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4730step1 raw4730step1Labels raw4730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw4731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw4731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw4731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4731 raw4731Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw4731 raw4731Labels = mixedMoment B raw4731step0 raw4731step0Labels := by
      have hz : ∀ j, raw4731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4731step0 = (fun i j => raw4731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4731step0 raw4731; decide +kernel
      have hl : raw4731step0Labels = raw4731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4731 raw4731Labels permutation346 hz
    mixedMoment B raw4731step0 raw4731step0Labels = mixedMoment B raw4731step1 raw4731step1Labels := by
      have hz : ∀ j, raw4731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4731step1 = (fun i j => raw4731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4731step1 raw4731step0; decide +kernel
      have hl : raw4731step1Labels = raw4731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4731step0 raw4731step0Labels permutation56 hz
    mixedMoment B raw4731step1 raw4731step1Labels = mixedMoment B raw4731step2 raw4731step2Labels := by
      have ha : raw4731step2 = (fun i j => raw4731step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4731step2 raw4731step1; decide +kernel
      have hl : raw4731step2Labels = raw4731step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4731step1 raw4731step1Labels permutation31 permutation7
    mixedMoment B raw4731step2 raw4731step2Labels = mixedMoment B raw4731step3 raw4731step3Labels := by
      have ha : raw4731step3 = raw4731step2 := by apply Matrix.ext; unfold raw4731step3 raw4731step2; decide +kernel
      have hl : raw4731step2Labels = labelEmbedding1 ∘ raw4731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4731step2 raw4731step2Labels raw4731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw4732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw4732step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4732step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4732step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw4732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4732 raw4732Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw4732 raw4732Labels = mixedMoment B raw4732step0 raw4732step0Labels := by
      have hz : ∀ j, raw4732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4732step0 = (fun i j => raw4732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4732step0 raw4732; decide +kernel
      have hl : raw4732step0Labels = raw4732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4732 raw4732Labels permutation346 hz
    mixedMoment B raw4732step0 raw4732step0Labels = mixedMoment B raw4732step1 raw4732step1Labels := by
      have hz : ∀ j, raw4732step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4732step1 = (fun i j => raw4732step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4732step1 raw4732step0; decide +kernel
      have hl : raw4732step1Labels = raw4732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4732step0 raw4732step0Labels permutation56 hz
    mixedMoment B raw4732step1 raw4732step1Labels = mixedMoment B raw4732step2 raw4732step2Labels := by
      have ha : raw4732step2 = (fun i j => raw4732step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4732step2 raw4732step1; decide +kernel
      have hl : raw4732step2Labels = raw4732step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4732step1 raw4732step1Labels permutation31 permutation7
    mixedMoment B raw4732step2 raw4732step2Labels = mixedMoment B raw4732step3 raw4732step3Labels := by
      have ha : raw4732step3 = raw4732step2 := by apply Matrix.ext; unfold raw4732step3 raw4732step2; decide +kernel
      have hl : raw4732step2Labels = labelEmbedding1 ∘ raw4732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4732step2 raw4732step2Labels raw4732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw4733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw4733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw4733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4733 raw4733Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw4733 raw4733Labels = mixedMoment B raw4733step0 raw4733step0Labels := by
      have hz : ∀ j, raw4733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4733step0 = (fun i j => raw4733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4733step0 raw4733; decide +kernel
      have hl : raw4733step0Labels = raw4733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4733 raw4733Labels permutation346 hz
    mixedMoment B raw4733step0 raw4733step0Labels = mixedMoment B raw4733step1 raw4733step1Labels := by
      have hz : ∀ j, raw4733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4733step1 = (fun i j => raw4733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4733step1 raw4733step0; decide +kernel
      have hl : raw4733step1Labels = raw4733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4733step0 raw4733step0Labels permutation56 hz
    mixedMoment B raw4733step1 raw4733step1Labels = mixedMoment B raw4733step2 raw4733step2Labels := by
      have ha : raw4733step2 = (fun i j => raw4733step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4733step2 raw4733step1; decide +kernel
      have hl : raw4733step2Labels = raw4733step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4733step1 raw4733step1Labels permutation8 permutation5
    mixedMoment B raw4733step2 raw4733step2Labels = mixedMoment B raw4733step3 raw4733step3Labels := by
      have ha : raw4733step3 = -raw4733step2 := by apply Matrix.ext; change ∀ i j, raw4733step3 i j = -(raw4733step2 i j); unfold raw4733step3 raw4733step2; decide +kernel
      have hl : raw4733step3Labels = raw4733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4733step3 raw4733step3Labels = mixedMoment B raw4733step4 raw4733step4Labels := by
      have ha : raw4733step4 = raw4733step3 := by apply Matrix.ext; unfold raw4733step4 raw4733step3; decide +kernel
      have hl : raw4733step3Labels = labelEmbedding1 ∘ raw4733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4733step3 raw4733step3Labels raw4733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw4734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4734 raw4734Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw4734 raw4734Labels = mixedMoment B raw4734step0 raw4734step0Labels := by
      have hz : ∀ j, raw4734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4734step0 = (fun i j => raw4734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4734step0 raw4734; decide +kernel
      have hl : raw4734step0Labels = raw4734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4734 raw4734Labels permutation346 hz
    mixedMoment B raw4734step0 raw4734step0Labels = mixedMoment B raw4734step1 raw4734step1Labels := by
      have ha : raw4734step1 = (fun i j => raw4734step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4734step1 raw4734step0; decide +kernel
      have hl : raw4734step1Labels = raw4734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4734step0 raw4734step0Labels permutation137 permutation7
    mixedMoment B raw4734step1 raw4734step1Labels = mixedMoment B raw4734step2 raw4734step2Labels := by
      have ha : raw4734step2 = raw4734step1 := by apply Matrix.ext; unfold raw4734step2 raw4734step1; decide +kernel
      have hl : raw4734step1Labels = labelEmbedding1 ∘ raw4734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4734step1 raw4734step1Labels raw4734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw4735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw4735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4735 raw4735Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw4735 raw4735Labels = mixedMoment B raw4735step0 raw4735step0Labels := by
      have hz : ∀ j, raw4735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4735step0 = (fun i j => raw4735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4735step0 raw4735; decide +kernel
      have hl : raw4735step0Labels = raw4735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4735 raw4735Labels permutation265 hz
    mixedMoment B raw4735step0 raw4735step0Labels = mixedMoment B raw4735step1 raw4735step1Labels := by
      have ha : raw4735step1 = (fun i j => raw4735step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4735step1 raw4735step0; decide +kernel
      have hl : raw4735step1Labels = raw4735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4735step0 raw4735step0Labels permutation137 permutation7
    mixedMoment B raw4735step1 raw4735step1Labels = mixedMoment B raw4735step2 raw4735step2Labels := by
      have ha : raw4735step2 = raw4735step1 := by apply Matrix.ext; unfold raw4735step2 raw4735step1; decide +kernel
      have hl : raw4735step1Labels = labelEmbedding1 ∘ raw4735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4735step1 raw4735step1Labels raw4735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
