import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8448step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8448 raw8448Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw8448 raw8448Labels = mixedMoment B raw8448step0 raw8448step0Labels := by
      have hz : ∀ j, raw8448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8448step0 = (fun i j => raw8448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8448step0 raw8448; decide +kernel
      have hl : raw8448step0Labels = raw8448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8448 raw8448Labels permutation265 hz
    mixedMoment B raw8448step0 raw8448step0Labels = mixedMoment B raw8448step1 raw8448step1Labels := by
      have ha : raw8448step1 = (fun i j => raw8448step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8448step1 raw8448step0; decide +kernel
      have hl : raw8448step1Labels = raw8448step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8448step0 raw8448step0Labels permutation46 permutation3
    mixedMoment B raw8448step1 raw8448step1Labels = mixedMoment B raw8448step2 raw8448step2Labels := by
      have ha : raw8448step2 = raw8448step1 := by apply Matrix.ext; unfold raw8448step2 raw8448step1; decide +kernel
      have hl : raw8448step1Labels = labelEmbedding6 ∘ raw8448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8448step1 raw8448step1Labels raw8448step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw8449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8449step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8449 raw8449Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8449 raw8449Labels = mixedMoment B raw8449step0 raw8449step0Labels := by
      have hz : ∀ j, raw8449 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8449step0 = (fun i j => raw8449 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8449step0 raw8449; decide +kernel
      have hl : raw8449step0Labels = raw8449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8449 raw8449Labels permutation265 hz
    mixedMoment B raw8449step0 raw8449step0Labels = mixedMoment B raw8449step1 raw8449step1Labels := by
      have ha : raw8449step1 = (fun i j => raw8449step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8449step1 raw8449step0; decide +kernel
      have hl : raw8449step1Labels = raw8449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8449step0 raw8449step0Labels permutation41 permutation3
    mixedMoment B raw8449step1 raw8449step1Labels = mixedMoment B raw8449step2 raw8449step2Labels := by
      have ha : raw8449step2 = raw8449step1 := by apply Matrix.ext; unfold raw8449step2 raw8449step1; decide +kernel
      have hl : raw8449step1Labels = labelEmbedding6 ∘ raw8449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8449step1 raw8449step1Labels raw8449step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8450 raw8450Labels = mixedMoment B node4492 node4492Labels := by
  calc
    mixedMoment B raw8450 raw8450Labels = mixedMoment B raw8450step0 raw8450step0Labels := by
      have hz : ∀ j, raw8450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8450step0 = (fun i j => raw8450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8450step0 raw8450; decide +kernel
      have hl : raw8450step0Labels = raw8450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8450 raw8450Labels permutation346 hz
    mixedMoment B raw8450step0 raw8450step0Labels = mixedMoment B raw8450step1 raw8450step1Labels := by
      have hz : ∀ j, raw8450step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8450step1 = (fun i j => raw8450step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8450step1 raw8450step0; decide +kernel
      have hl : raw8450step1Labels = raw8450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8450step0 raw8450step0Labels permutation56 hz
    mixedMoment B raw8450step1 raw8450step1Labels = mixedMoment B raw8450step2 raw8450step2Labels := by
      have ha : raw8450step2 = (fun i j => raw8450step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8450step2 raw8450step1; decide +kernel
      have hl : raw8450step2Labels = raw8450step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8450step1 raw8450step1Labels permutation10 permutation3
    mixedMoment B raw8450step2 raw8450step2Labels = mixedMoment B raw8450step3 raw8450step3Labels := by
      have ha : raw8450step3 = raw8450step2 := by apply Matrix.ext; unfold raw8450step3 raw8450step2; decide +kernel
      have hl : raw8450step2Labels = labelEmbedding6 ∘ raw8450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8450step2 raw8450step2Labels raw8450step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4492 node4492Labels := by rfl

def raw8451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8451 raw8451Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw8451 raw8451Labels = mixedMoment B raw8451step0 raw8451step0Labels := by
      have hz : ∀ j, raw8451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8451step0 = (fun i j => raw8451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8451step0 raw8451; decide +kernel
      have hl : raw8451step0Labels = raw8451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8451 raw8451Labels permutation346 hz
    mixedMoment B raw8451step0 raw8451step0Labels = mixedMoment B raw8451step1 raw8451step1Labels := by
      have ha : raw8451step1 = (fun i j => raw8451step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8451step1 raw8451step0; decide +kernel
      have hl : raw8451step1Labels = raw8451step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8451step0 raw8451step0Labels permutation34 permutation3
    mixedMoment B raw8451step1 raw8451step1Labels = mixedMoment B raw8451step2 raw8451step2Labels := by
      have ha : raw8451step2 = raw8451step1 := by apply Matrix.ext; unfold raw8451step2 raw8451step1; decide +kernel
      have hl : raw8451step1Labels = labelEmbedding6 ∘ raw8451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8451step1 raw8451step1Labels raw8451step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw8452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8452step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8452 raw8452Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw8452 raw8452Labels = mixedMoment B raw8452step0 raw8452step0Labels := by
      have hz : ∀ j, raw8452 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8452step0 = (fun i j => raw8452 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8452step0 raw8452; decide +kernel
      have hl : raw8452step0Labels = raw8452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8452 raw8452Labels permutation265 hz
    mixedMoment B raw8452step0 raw8452step0Labels = mixedMoment B raw8452step1 raw8452step1Labels := by
      have ha : raw8452step1 = (fun i j => raw8452step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8452step1 raw8452step0; decide +kernel
      have hl : raw8452step1Labels = raw8452step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8452step0 raw8452step0Labels permutation34 permutation3
    mixedMoment B raw8452step1 raw8452step1Labels = mixedMoment B raw8452step2 raw8452step2Labels := by
      have ha : raw8452step2 = raw8452step1 := by apply Matrix.ext; unfold raw8452step2 raw8452step1; decide +kernel
      have hl : raw8452step1Labels = labelEmbedding6 ∘ raw8452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8452step1 raw8452step1Labels raw8452step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw8453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8453step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8453 raw8453Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw8453 raw8453Labels = mixedMoment B raw8453step0 raw8453step0Labels := by
      have hz : ∀ j, raw8453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8453step0 = (fun i j => raw8453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8453step0 raw8453; decide +kernel
      have hl : raw8453step0Labels = raw8453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8453 raw8453Labels permutation346 hz
    mixedMoment B raw8453step0 raw8453step0Labels = mixedMoment B raw8453step1 raw8453step1Labels := by
      have hz : ∀ j, raw8453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8453step1 = (fun i j => raw8453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8453step1 raw8453step0; decide +kernel
      have hl : raw8453step1Labels = raw8453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8453step0 raw8453step0Labels permutation56 hz
    mixedMoment B raw8453step1 raw8453step1Labels = mixedMoment B raw8453step2 raw8453step2Labels := by
      have ha : raw8453step2 = (fun i j => raw8453step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8453step2 raw8453step1; decide +kernel
      have hl : raw8453step2Labels = raw8453step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8453step1 raw8453step1Labels permutation18 permutation4
    mixedMoment B raw8453step2 raw8453step2Labels = mixedMoment B raw8453step3 raw8453step3Labels := by
      have ha : raw8453step3 = raw8453step2 := by apply Matrix.ext; unfold raw8453step3 raw8453step2; decide +kernel
      have hl : raw8453step2Labels = labelEmbedding7 ∘ raw8453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8453step2 raw8453step2Labels raw8453step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw8454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8454step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8454 raw8454Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw8454 raw8454Labels = mixedMoment B raw8454step0 raw8454step0Labels := by
      have hz : ∀ j, raw8454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8454step0 = (fun i j => raw8454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8454step0 raw8454; decide +kernel
      have hl : raw8454step0Labels = raw8454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8454 raw8454Labels permutation346 hz
    mixedMoment B raw8454step0 raw8454step0Labels = mixedMoment B raw8454step1 raw8454step1Labels := by
      have hz : ∀ j, raw8454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8454step1 = (fun i j => raw8454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8454step1 raw8454step0; decide +kernel
      have hl : raw8454step1Labels = raw8454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8454step0 raw8454step0Labels permutation56 hz
    mixedMoment B raw8454step1 raw8454step1Labels = mixedMoment B raw8454step2 raw8454step2Labels := by
      have ha : raw8454step2 = (fun i j => raw8454step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8454step2 raw8454step1; decide +kernel
      have hl : raw8454step2Labels = raw8454step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8454step1 raw8454step1Labels permutation19 permutation4
    mixedMoment B raw8454step2 raw8454step2Labels = mixedMoment B raw8454step3 raw8454step3Labels := by
      have ha : raw8454step3 = raw8454step2 := by apply Matrix.ext; unfold raw8454step3 raw8454step2; decide +kernel
      have hl : raw8454step2Labels = labelEmbedding7 ∘ raw8454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8454step2 raw8454step2Labels raw8454step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw8455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8455step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8455step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8455 raw8455Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw8455 raw8455Labels = mixedMoment B raw8455step0 raw8455step0Labels := by
      have hz : ∀ j, raw8455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8455step0 = (fun i j => raw8455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8455step0 raw8455; decide +kernel
      have hl : raw8455step0Labels = raw8455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8455 raw8455Labels permutation346 hz
    mixedMoment B raw8455step0 raw8455step0Labels = mixedMoment B raw8455step1 raw8455step1Labels := by
      have hz : ∀ j, raw8455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8455step1 = (fun i j => raw8455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8455step1 raw8455step0; decide +kernel
      have hl : raw8455step1Labels = raw8455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8455step0 raw8455step0Labels permutation56 hz
    mixedMoment B raw8455step1 raw8455step1Labels = mixedMoment B raw8455step2 raw8455step2Labels := by
      have ha : raw8455step2 = (fun i j => raw8455step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8455step2 raw8455step1; decide +kernel
      have hl : raw8455step2Labels = raw8455step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8455step1 raw8455step1Labels permutation8 permutation3
    mixedMoment B raw8455step2 raw8455step2Labels = mixedMoment B raw8455step3 raw8455step3Labels := by
      have ha : raw8455step3 = raw8455step2 := by apply Matrix.ext; unfold raw8455step3 raw8455step2; decide +kernel
      have hl : raw8455step2Labels = labelEmbedding6 ∘ raw8455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8455step2 raw8455step2Labels raw8455step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw8456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8456step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8456 raw8456Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw8456 raw8456Labels = mixedMoment B raw8456step0 raw8456step0Labels := by
      have hz : ∀ j, raw8456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8456step0 = (fun i j => raw8456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8456step0 raw8456; decide +kernel
      have hl : raw8456step0Labels = raw8456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8456 raw8456Labels permutation346 hz
    mixedMoment B raw8456step0 raw8456step0Labels = mixedMoment B raw8456step1 raw8456step1Labels := by
      have ha : raw8456step1 = (fun i j => raw8456step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8456step1 raw8456step0; decide +kernel
      have hl : raw8456step1Labels = raw8456step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8456step0 raw8456step0Labels permutation32 permutation3
    mixedMoment B raw8456step1 raw8456step1Labels = mixedMoment B raw8456step2 raw8456step2Labels := by
      have ha : raw8456step2 = raw8456step1 := by apply Matrix.ext; unfold raw8456step2 raw8456step1; decide +kernel
      have hl : raw8456step1Labels = labelEmbedding6 ∘ raw8456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8456step1 raw8456step1Labels raw8456step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw8457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8457 raw8457Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw8457 raw8457Labels = mixedMoment B raw8457step0 raw8457step0Labels := by
      have hz : ∀ j, raw8457 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8457step0 = (fun i j => raw8457 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8457step0 raw8457; decide +kernel
      have hl : raw8457step0Labels = raw8457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8457 raw8457Labels permutation265 hz
    mixedMoment B raw8457step0 raw8457step0Labels = mixedMoment B raw8457step1 raw8457step1Labels := by
      have ha : raw8457step1 = (fun i j => raw8457step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8457step1 raw8457step0; decide +kernel
      have hl : raw8457step1Labels = raw8457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8457step0 raw8457step0Labels permutation32 permutation3
    mixedMoment B raw8457step1 raw8457step1Labels = mixedMoment B raw8457step2 raw8457step2Labels := by
      have ha : raw8457step2 = raw8457step1 := by apply Matrix.ext; unfold raw8457step2 raw8457step1; decide +kernel
      have hl : raw8457step1Labels = labelEmbedding6 ∘ raw8457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8457step1 raw8457step1Labels raw8457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw8458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8458step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8458 raw8458Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw8458 raw8458Labels = mixedMoment B raw8458step0 raw8458step0Labels := by
      have hz : ∀ j, raw8458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8458step0 = (fun i j => raw8458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8458step0 raw8458; decide +kernel
      have hl : raw8458step0Labels = raw8458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8458 raw8458Labels permutation346 hz
    mixedMoment B raw8458step0 raw8458step0Labels = mixedMoment B raw8458step1 raw8458step1Labels := by
      have hz : ∀ j, raw8458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8458step1 = (fun i j => raw8458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8458step1 raw8458step0; decide +kernel
      have hl : raw8458step1Labels = raw8458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8458step0 raw8458step0Labels permutation56 hz
    mixedMoment B raw8458step1 raw8458step1Labels = mixedMoment B raw8458step2 raw8458step2Labels := by
      have ha : raw8458step2 = (fun i j => raw8458step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8458step2 raw8458step1; decide +kernel
      have hl : raw8458step2Labels = raw8458step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8458step1 raw8458step1Labels permutation8 permutation3
    mixedMoment B raw8458step2 raw8458step2Labels = mixedMoment B raw8458step3 raw8458step3Labels := by
      have ha : raw8458step3 = raw8458step2 := by apply Matrix.ext; unfold raw8458step3 raw8458step2; decide +kernel
      have hl : raw8458step2Labels = labelEmbedding6 ∘ raw8458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8458step2 raw8458step2Labels raw8458step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw8459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8459step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8459step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8459 raw8459Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8459 raw8459Labels = mixedMoment B raw8459step0 raw8459step0Labels := by
      have hz : ∀ j, raw8459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8459step0 = (fun i j => raw8459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8459step0 raw8459; decide +kernel
      have hl : raw8459step0Labels = raw8459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8459 raw8459Labels permutation346 hz
    mixedMoment B raw8459step0 raw8459step0Labels = mixedMoment B raw8459step1 raw8459step1Labels := by
      have hz : ∀ j, raw8459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8459step1 = (fun i j => raw8459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8459step1 raw8459step0; decide +kernel
      have hl : raw8459step1Labels = raw8459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8459step0 raw8459step0Labels permutation56 hz
    mixedMoment B raw8459step1 raw8459step1Labels = mixedMoment B raw8459step2 raw8459step2Labels := by
      have ha : raw8459step2 = (fun i j => raw8459step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8459step2 raw8459step1; decide +kernel
      have hl : raw8459step2Labels = raw8459step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8459step1 raw8459step1Labels permutation9 permutation3
    mixedMoment B raw8459step2 raw8459step2Labels = mixedMoment B raw8459step3 raw8459step3Labels := by
      have ha : raw8459step3 = raw8459step2 := by apply Matrix.ext; unfold raw8459step3 raw8459step2; decide +kernel
      have hl : raw8459step2Labels = labelEmbedding6 ∘ raw8459step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8459step2 raw8459step2Labels raw8459step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8460step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8460 raw8460Labels = mixedMoment B node4472 node4472Labels := by
  calc
    mixedMoment B raw8460 raw8460Labels = mixedMoment B raw8460step0 raw8460step0Labels := by
      have hz : ∀ j, raw8460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8460step0 = (fun i j => raw8460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8460step0 raw8460; decide +kernel
      have hl : raw8460step0Labels = raw8460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8460 raw8460Labels permutation346 hz
    mixedMoment B raw8460step0 raw8460step0Labels = mixedMoment B raw8460step1 raw8460step1Labels := by
      have hz : ∀ j, raw8460step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8460step1 = (fun i j => raw8460step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8460step1 raw8460step0; decide +kernel
      have hl : raw8460step1Labels = raw8460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8460step0 raw8460step0Labels permutation56 hz
    mixedMoment B raw8460step1 raw8460step1Labels = mixedMoment B raw8460step2 raw8460step2Labels := by
      have ha : raw8460step2 = (fun i j => raw8460step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8460step2 raw8460step1; decide +kernel
      have hl : raw8460step2Labels = raw8460step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8460step1 raw8460step1Labels permutation8 permutation3
    mixedMoment B raw8460step2 raw8460step2Labels = mixedMoment B raw8460step3 raw8460step3Labels := by
      have ha : raw8460step3 = raw8460step2 := by apply Matrix.ext; unfold raw8460step3 raw8460step2; decide +kernel
      have hl : raw8460step2Labels = labelEmbedding6 ∘ raw8460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8460step2 raw8460step2Labels raw8460step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4472 node4472Labels := by rfl

def raw8461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8461 raw8461Labels = mixedMoment B node5084 node5084Labels := by
  calc
    mixedMoment B raw8461 raw8461Labels = mixedMoment B raw8461step0 raw8461step0Labels := by
      have hz : ∀ j, raw8461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8461step0 = (fun i j => raw8461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8461step0 raw8461; decide +kernel
      have hl : raw8461step0Labels = raw8461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8461 raw8461Labels permutation346 hz
    mixedMoment B raw8461step0 raw8461step0Labels = mixedMoment B raw8461step1 raw8461step1Labels := by
      have ha : raw8461step1 = (fun i j => raw8461step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8461step1 raw8461step0; decide +kernel
      have hl : raw8461step1Labels = raw8461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8461step0 raw8461step0Labels permutation32 permutation3
    mixedMoment B raw8461step1 raw8461step1Labels = mixedMoment B raw8461step2 raw8461step2Labels := by
      have ha : raw8461step2 = raw8461step1 := by apply Matrix.ext; unfold raw8461step2 raw8461step1; decide +kernel
      have hl : raw8461step1Labels = labelEmbedding6 ∘ raw8461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8461step1 raw8461step1Labels raw8461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5084 node5084Labels := by rfl

def raw8462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8462 raw8462Labels = mixedMoment B node5084 node5084Labels := by
  calc
    mixedMoment B raw8462 raw8462Labels = mixedMoment B raw8462step0 raw8462step0Labels := by
      have hz : ∀ j, raw8462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8462step0 = (fun i j => raw8462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8462step0 raw8462; decide +kernel
      have hl : raw8462step0Labels = raw8462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8462 raw8462Labels permutation265 hz
    mixedMoment B raw8462step0 raw8462step0Labels = mixedMoment B raw8462step1 raw8462step1Labels := by
      have ha : raw8462step1 = (fun i j => raw8462step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8462step1 raw8462step0; decide +kernel
      have hl : raw8462step1Labels = raw8462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8462step0 raw8462step0Labels permutation32 permutation3
    mixedMoment B raw8462step1 raw8462step1Labels = mixedMoment B raw8462step2 raw8462step2Labels := by
      have ha : raw8462step2 = raw8462step1 := by apply Matrix.ext; unfold raw8462step2 raw8462step1; decide +kernel
      have hl : raw8462step1Labels = labelEmbedding6 ∘ raw8462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8462step1 raw8462step1Labels raw8462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5084 node5084Labels := by rfl

def raw8463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8463step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8463step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8463step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8463step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8463 raw8463Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw8463 raw8463Labels = mixedMoment B raw8463step0 raw8463step0Labels := by
      have hz : ∀ j, raw8463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8463step0 = (fun i j => raw8463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8463step0 raw8463; decide +kernel
      have hl : raw8463step0Labels = raw8463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8463 raw8463Labels permutation346 hz
    mixedMoment B raw8463step0 raw8463step0Labels = mixedMoment B raw8463step1 raw8463step1Labels := by
      have hz : ∀ j, raw8463step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8463step1 = (fun i j => raw8463step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8463step1 raw8463step0; decide +kernel
      have hl : raw8463step1Labels = raw8463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8463step0 raw8463step0Labels permutation56 hz
    mixedMoment B raw8463step1 raw8463step1Labels = mixedMoment B raw8463step2 raw8463step2Labels := by
      have ha : raw8463step2 = (fun i j => raw8463step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8463step2 raw8463step1; decide +kernel
      have hl : raw8463step2Labels = raw8463step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8463step1 raw8463step1Labels permutation8 permutation3
    mixedMoment B raw8463step2 raw8463step2Labels = mixedMoment B raw8463step3 raw8463step3Labels := by
      have ha : raw8463step3 = raw8463step2 := by apply Matrix.ext; unfold raw8463step3 raw8463step2; decide +kernel
      have hl : raw8463step2Labels = labelEmbedding6 ∘ raw8463step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8463step2 raw8463step2Labels raw8463step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5201 node5201Labels := by rfl

def raw8464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8464step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw8464step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8464step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw8464step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8464 raw8464Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw8464 raw8464Labels = mixedMoment B raw8464step0 raw8464step0Labels := by
      have hz : ∀ j, raw8464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8464step0 = (fun i j => raw8464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8464step0 raw8464; decide +kernel
      have hl : raw8464step0Labels = raw8464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8464 raw8464Labels permutation346 hz
    mixedMoment B raw8464step0 raw8464step0Labels = mixedMoment B raw8464step1 raw8464step1Labels := by
      have hz : ∀ j, raw8464step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8464step1 = (fun i j => raw8464step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8464step1 raw8464step0; decide +kernel
      have hl : raw8464step1Labels = raw8464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8464step0 raw8464step0Labels permutation56 hz
    mixedMoment B raw8464step1 raw8464step1Labels = mixedMoment B raw8464step2 raw8464step2Labels := by
      have ha : raw8464step2 = (fun i j => raw8464step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8464step2 raw8464step1; decide +kernel
      have hl : raw8464step2Labels = raw8464step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8464step1 raw8464step1Labels permutation10 permutation3
    mixedMoment B raw8464step2 raw8464step2Labels = mixedMoment B raw8464step3 raw8464step3Labels := by
      have ha : raw8464step3 = raw8464step2 := by apply Matrix.ext; unfold raw8464step3 raw8464step2; decide +kernel
      have hl : raw8464step2Labels = labelEmbedding6 ∘ raw8464step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8464step2 raw8464step2Labels raw8464step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw8465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8465 raw8465Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8465 raw8465Labels = mixedMoment B raw8465step0 raw8465step0Labels := by
      have hz : ∀ j, raw8465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8465step0 = (fun i j => raw8465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8465step0 raw8465; decide +kernel
      have hl : raw8465step0Labels = raw8465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8465 raw8465Labels permutation346 hz
    mixedMoment B raw8465step0 raw8465step0Labels = mixedMoment B raw8465step1 raw8465step1Labels := by
      have ha : raw8465step1 = (fun i j => raw8465step0 (permutation81 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8465step1 raw8465step0; decide +kernel
      have hl : raw8465step1Labels = raw8465step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8465step0 raw8465step0Labels permutation81 permutation6
    mixedMoment B raw8465step1 raw8465step1Labels = mixedMoment B raw8465step2 raw8465step2Labels := by
      have ha : raw8465step2 = -raw8465step1 := by apply Matrix.ext; change ∀ i j, raw8465step2 i j = -(raw8465step1 i j); unfold raw8465step2 raw8465step1; decide +kernel
      have hl : raw8465step2Labels = raw8465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw8466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw8466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8466 raw8466Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw8466 raw8466Labels = mixedMoment B raw8466step0 raw8466step0Labels := by
      have hz : ∀ j, raw8466 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8466step0 = (fun i j => raw8466 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8466step0 raw8466; decide +kernel
      have hl : raw8466step0Labels = raw8466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8466 raw8466Labels permutation265 hz
    mixedMoment B raw8466step0 raw8466step0Labels = mixedMoment B raw8466step1 raw8466step1Labels := by
      have ha : raw8466step1 = (fun i j => raw8466step0 (permutation81 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8466step1 raw8466step0; decide +kernel
      have hl : raw8466step1Labels = raw8466step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8466step0 raw8466step0Labels permutation81 permutation6
    mixedMoment B raw8466step1 raw8466step1Labels = mixedMoment B raw8466step2 raw8466step2Labels := by
      have ha : raw8466step2 = -raw8466step1 := by apply Matrix.ext; change ∀ i j, raw8466step2 i j = -(raw8466step1 i j); unfold raw8466step2 raw8466step1; decide +kernel
      have hl : raw8466step2Labels = raw8466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw8467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8467step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8467 raw8467Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw8467 raw8467Labels = mixedMoment B raw8467step0 raw8467step0Labels := by
      have hz : ∀ j, raw8467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8467step0 = (fun i j => raw8467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8467step0 raw8467; decide +kernel
      have hl : raw8467step0Labels = raw8467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8467 raw8467Labels permutation346 hz
    mixedMoment B raw8467step0 raw8467step0Labels = mixedMoment B raw8467step1 raw8467step1Labels := by
      have hz : ∀ j, raw8467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8467step1 = (fun i j => raw8467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8467step1 raw8467step0; decide +kernel
      have hl : raw8467step1Labels = raw8467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8467step0 raw8467step0Labels permutation56 hz
    mixedMoment B raw8467step1 raw8467step1Labels = mixedMoment B raw8467step2 raw8467step2Labels := by
      have ha : raw8467step2 = (fun i j => raw8467step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8467step2 raw8467step1; decide +kernel
      have hl : raw8467step2Labels = raw8467step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8467step1 raw8467step1Labels permutation8 permutation3
    _ = mixedMoment B node4004 node4004Labels := by rfl

def raw8468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8468step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8468 raw8468Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw8468 raw8468Labels = mixedMoment B raw8468step0 raw8468step0Labels := by
      have hz : ∀ j, raw8468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8468step0 = (fun i j => raw8468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8468step0 raw8468; decide +kernel
      have hl : raw8468step0Labels = raw8468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8468 raw8468Labels permutation346 hz
    mixedMoment B raw8468step0 raw8468step0Labels = mixedMoment B raw8468step1 raw8468step1Labels := by
      have hz : ∀ j, raw8468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8468step1 = (fun i j => raw8468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8468step1 raw8468step0; decide +kernel
      have hl : raw8468step1Labels = raw8468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8468step0 raw8468step0Labels permutation56 hz
    mixedMoment B raw8468step1 raw8468step1Labels = mixedMoment B raw8468step2 raw8468step2Labels := by
      have ha : raw8468step2 = (fun i j => raw8468step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8468step2 raw8468step1; decide +kernel
      have hl : raw8468step2Labels = raw8468step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8468step1 raw8468step1Labels permutation24 permutation6
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw8469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8469step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8469step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8469 raw8469Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw8469 raw8469Labels = mixedMoment B raw8469step0 raw8469step0Labels := by
      have hz : ∀ j, raw8469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8469step0 = (fun i j => raw8469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8469step0 raw8469; decide +kernel
      have hl : raw8469step0Labels = raw8469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8469 raw8469Labels permutation346 hz
    mixedMoment B raw8469step0 raw8469step0Labels = mixedMoment B raw8469step1 raw8469step1Labels := by
      have hz : ∀ j, raw8469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8469step1 = (fun i j => raw8469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8469step1 raw8469step0; decide +kernel
      have hl : raw8469step1Labels = raw8469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8469step0 raw8469step0Labels permutation56 hz
    mixedMoment B raw8469step1 raw8469step1Labels = mixedMoment B raw8469step2 raw8469step2Labels := by
      have ha : raw8469step2 = (fun i j => raw8469step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8469step2 raw8469step1; decide +kernel
      have hl : raw8469step2Labels = raw8469step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8469step1 raw8469step1Labels permutation15 permutation6
    mixedMoment B raw8469step2 raw8469step2Labels = mixedMoment B raw8469step3 raw8469step3Labels := by
      have ha : raw8469step3 = -raw8469step2 := by apply Matrix.ext; change ∀ i j, raw8469step3 i j = -(raw8469step2 i j); unfold raw8469step3 raw8469step2; decide +kernel
      have hl : raw8469step3Labels = raw8469step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw8470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8470 raw8470Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw8470 raw8470Labels = mixedMoment B raw8470step0 raw8470step0Labels := by
      have hz : ∀ j, raw8470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8470step0 = (fun i j => raw8470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8470step0 raw8470; decide +kernel
      have hl : raw8470step0Labels = raw8470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8470 raw8470Labels permutation346 hz
    mixedMoment B raw8470step0 raw8470step0Labels = mixedMoment B raw8470step1 raw8470step1Labels := by
      have ha : raw8470step1 = (fun i j => raw8470step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8470step1 raw8470step0; decide +kernel
      have hl : raw8470step1Labels = raw8470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8470step0 raw8470step0Labels permutation40 permutation3
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw8471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8471 raw8471Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw8471 raw8471Labels = mixedMoment B raw8471step0 raw8471step0Labels := by
      have ha : raw8471step0 = (fun i j => raw8471 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8471step0 raw8471; decide +kernel
      have hl : raw8471step0Labels = raw8471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8471 raw8471Labels permutation184 permutation3
    _ = mixedMoment B node2491 node2491Labels := by rfl

def raw8472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8472 raw8472Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8472 raw8472Labels = mixedMoment B raw8472step0 raw8472step0Labels := by
      have hz : ∀ j, raw8472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8472step0 = (fun i j => raw8472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8472step0 raw8472; decide +kernel
      have hl : raw8472step0Labels = raw8472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8472 raw8472Labels permutation346 hz
    mixedMoment B raw8472step0 raw8472step0Labels = mixedMoment B raw8472step1 raw8472step1Labels := by
      have ha : raw8472step1 = (fun i j => raw8472step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8472step1 raw8472step0; decide +kernel
      have hl : raw8472step1Labels = raw8472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8472step0 raw8472step0Labels permutation40 permutation3
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw8473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8473 raw8473Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw8473 raw8473Labels = mixedMoment B raw8473step0 raw8473step0Labels := by
      have hz : ∀ j, raw8473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8473step0 = (fun i j => raw8473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8473step0 raw8473; decide +kernel
      have hl : raw8473step0Labels = raw8473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8473 raw8473Labels permutation346 hz
    mixedMoment B raw8473step0 raw8473step0Labels = mixedMoment B raw8473step1 raw8473step1Labels := by
      have ha : raw8473step1 = (fun i j => raw8473step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8473step1 raw8473step0; decide +kernel
      have hl : raw8473step1Labels = raw8473step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8473step0 raw8473step0Labels permutation46 permutation3
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw8474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8474 raw8474Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8474 raw8474Labels = mixedMoment B raw8474step0 raw8474step0Labels := by
      have hz : ∀ j, raw8474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8474step0 = (fun i j => raw8474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8474step0 raw8474; decide +kernel
      have hl : raw8474step0Labels = raw8474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8474 raw8474Labels permutation346 hz
    mixedMoment B raw8474step0 raw8474step0Labels = mixedMoment B raw8474step1 raw8474step1Labels := by
      have ha : raw8474step1 = (fun i j => raw8474step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8474step1 raw8474step0; decide +kernel
      have hl : raw8474step1Labels = raw8474step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8474step0 raw8474step0Labels permutation41 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8475 raw8475Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw8475 raw8475Labels = mixedMoment B raw8475step0 raw8475step0Labels := by
      have hz : ∀ j, raw8475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8475step0 = (fun i j => raw8475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8475step0 raw8475; decide +kernel
      have hl : raw8475step0Labels = raw8475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8475 raw8475Labels permutation265 hz
    mixedMoment B raw8475step0 raw8475step0Labels = mixedMoment B raw8475step1 raw8475step1Labels := by
      have ha : raw8475step1 = (fun i j => raw8475step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8475step1 raw8475step0; decide +kernel
      have hl : raw8475step1Labels = raw8475step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8475step0 raw8475step0Labels permutation40 permutation3
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw8476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8476 raw8476Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw8476 raw8476Labels = mixedMoment B raw8476step0 raw8476step0Labels := by
      have ha : raw8476step0 = (fun i j => raw8476 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8476step0 raw8476; decide +kernel
      have hl : raw8476step0Labels = raw8476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8476 raw8476Labels permutation160 permutation3
    _ = mixedMoment B node2491 node2491Labels := by rfl

def raw8477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8477 raw8477Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw8477 raw8477Labels = mixedMoment B raw8477step0 raw8477step0Labels := by
      have hz : ∀ j, raw8477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8477step0 = (fun i j => raw8477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8477step0 raw8477; decide +kernel
      have hl : raw8477step0Labels = raw8477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8477 raw8477Labels permutation265 hz
    mixedMoment B raw8477step0 raw8477step0Labels = mixedMoment B raw8477step1 raw8477step1Labels := by
      have ha : raw8477step1 = (fun i j => raw8477step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8477step1 raw8477step0; decide +kernel
      have hl : raw8477step1Labels = raw8477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8477step0 raw8477step0Labels permutation40 permutation3
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw8478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw8478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8478 raw8478Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw8478 raw8478Labels = mixedMoment B raw8478step0 raw8478step0Labels := by
      have hz : ∀ j, raw8478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8478step0 = (fun i j => raw8478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8478step0 raw8478; decide +kernel
      have hl : raw8478step0Labels = raw8478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8478 raw8478Labels permutation265 hz
    mixedMoment B raw8478step0 raw8478step0Labels = mixedMoment B raw8478step1 raw8478step1Labels := by
      have ha : raw8478step1 = (fun i j => raw8478step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8478step1 raw8478step0; decide +kernel
      have hl : raw8478step1Labels = raw8478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8478step0 raw8478step0Labels permutation46 permutation3
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw8479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8479 raw8479Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8479 raw8479Labels = mixedMoment B raw8479step0 raw8479step0Labels := by
      have hz : ∀ j, raw8479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8479step0 = (fun i j => raw8479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8479step0 raw8479; decide +kernel
      have hl : raw8479step0Labels = raw8479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8479 raw8479Labels permutation265 hz
    mixedMoment B raw8479step0 raw8479step0Labels = mixedMoment B raw8479step1 raw8479step1Labels := by
      have ha : raw8479step1 = (fun i j => raw8479step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8479step1 raw8479step0; decide +kernel
      have hl : raw8479step1Labels = raw8479step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8479step0 raw8479step0Labels permutation41 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8480 raw8480Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw8480 raw8480Labels = mixedMoment B raw8480step0 raw8480step0Labels := by
      have hz : ∀ j, raw8480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8480step0 = (fun i j => raw8480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8480step0 raw8480; decide +kernel
      have hl : raw8480step0Labels = raw8480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8480 raw8480Labels permutation346 hz
    mixedMoment B raw8480step0 raw8480step0Labels = mixedMoment B raw8480step1 raw8480step1Labels := by
      have hz : ∀ j, raw8480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8480step1 = (fun i j => raw8480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8480step1 raw8480step0; decide +kernel
      have hl : raw8480step1Labels = raw8480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8480step0 raw8480step0Labels permutation56 hz
    mixedMoment B raw8480step1 raw8480step1Labels = mixedMoment B raw8480step2 raw8480step2Labels := by
      have ha : raw8480step2 = (fun i j => raw8480step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8480step2 raw8480step1; decide +kernel
      have hl : raw8480step2Labels = raw8480step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8480step1 raw8480step1Labels permutation10 permutation3
    _ = mixedMoment B node1076 node1076Labels := by rfl

def raw8481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8481 raw8481Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8481 raw8481Labels = mixedMoment B raw8481step0 raw8481step0Labels := by
      have hz : ∀ j, raw8481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8481step0 = (fun i j => raw8481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8481step0 raw8481; decide +kernel
      have hl : raw8481step0Labels = raw8481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8481 raw8481Labels permutation346 hz
    mixedMoment B raw8481step0 raw8481step0Labels = mixedMoment B raw8481step1 raw8481step1Labels := by
      have ha : raw8481step1 = (fun i j => raw8481step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8481step1 raw8481step0; decide +kernel
      have hl : raw8481step1Labels = raw8481step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8481step0 raw8481step0Labels permutation34 permutation3
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw8482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8482 raw8482Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8482 raw8482Labels = mixedMoment B raw8482step0 raw8482step0Labels := by
      have hz : ∀ j, raw8482 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8482step0 = (fun i j => raw8482 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8482step0 raw8482; decide +kernel
      have hl : raw8482step0Labels = raw8482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8482 raw8482Labels permutation265 hz
    mixedMoment B raw8482step0 raw8482step0Labels = mixedMoment B raw8482step1 raw8482step1Labels := by
      have ha : raw8482step1 = (fun i j => raw8482step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8482step1 raw8482step0; decide +kernel
      have hl : raw8482step1Labels = raw8482step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8482step0 raw8482step0Labels permutation34 permutation3
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw8483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8483 raw8483Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw8483 raw8483Labels = mixedMoment B raw8483step0 raw8483step0Labels := by
      have hz : ∀ j, raw8483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8483step0 = (fun i j => raw8483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8483step0 raw8483; decide +kernel
      have hl : raw8483step0Labels = raw8483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8483 raw8483Labels permutation346 hz
    mixedMoment B raw8483step0 raw8483step0Labels = mixedMoment B raw8483step1 raw8483step1Labels := by
      have hz : ∀ j, raw8483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8483step1 = (fun i j => raw8483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8483step1 raw8483step0; decide +kernel
      have hl : raw8483step1Labels = raw8483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8483step0 raw8483step0Labels permutation56 hz
    mixedMoment B raw8483step1 raw8483step1Labels = mixedMoment B raw8483step2 raw8483step2Labels := by
      have ha : raw8483step2 = (fun i j => raw8483step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8483step2 raw8483step1; decide +kernel
      have hl : raw8483step2Labels = raw8483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8483step1 raw8483step1Labels permutation10 permutation3
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw8484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8484 raw8484Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw8484 raw8484Labels = mixedMoment B raw8484step0 raw8484step0Labels := by
      have hz : ∀ j, raw8484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8484step0 = (fun i j => raw8484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8484step0 raw8484; decide +kernel
      have hl : raw8484step0Labels = raw8484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8484 raw8484Labels permutation346 hz
    mixedMoment B raw8484step0 raw8484step0Labels = mixedMoment B raw8484step1 raw8484step1Labels := by
      have hz : ∀ j, raw8484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8484step1 = (fun i j => raw8484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8484step1 raw8484step0; decide +kernel
      have hl : raw8484step1Labels = raw8484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8484step0 raw8484step0Labels permutation56 hz
    mixedMoment B raw8484step1 raw8484step1Labels = mixedMoment B raw8484step2 raw8484step2Labels := by
      have ha : raw8484step2 = (fun i j => raw8484step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8484step2 raw8484step1; decide +kernel
      have hl : raw8484step2Labels = raw8484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8484step1 raw8484step1Labels permutation11 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw8485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8485 raw8485Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw8485 raw8485Labels = mixedMoment B raw8485step0 raw8485step0Labels := by
      have hz : ∀ j, raw8485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8485step0 = (fun i j => raw8485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8485step0 raw8485; decide +kernel
      have hl : raw8485step0Labels = raw8485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8485 raw8485Labels permutation346 hz
    mixedMoment B raw8485step0 raw8485step0Labels = mixedMoment B raw8485step1 raw8485step1Labels := by
      have hz : ∀ j, raw8485step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8485step1 = (fun i j => raw8485step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8485step1 raw8485step0; decide +kernel
      have hl : raw8485step1Labels = raw8485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8485step0 raw8485step0Labels permutation56 hz
    mixedMoment B raw8485step1 raw8485step1Labels = mixedMoment B raw8485step2 raw8485step2Labels := by
      have ha : raw8485step2 = (fun i j => raw8485step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8485step2 raw8485step1; decide +kernel
      have hl : raw8485step2Labels = raw8485step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8485step1 raw8485step1Labels permutation8 permutation3
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw8486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8486 raw8486Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw8486 raw8486Labels = mixedMoment B raw8486step0 raw8486step0Labels := by
      have hz : ∀ j, raw8486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8486step0 = (fun i j => raw8486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8486step0 raw8486; decide +kernel
      have hl : raw8486step0Labels = raw8486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8486 raw8486Labels permutation346 hz
    mixedMoment B raw8486step0 raw8486step0Labels = mixedMoment B raw8486step1 raw8486step1Labels := by
      have ha : raw8486step1 = (fun i j => raw8486step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8486step1 raw8486step0; decide +kernel
      have hl : raw8486step1Labels = raw8486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8486step0 raw8486step0Labels permutation32 permutation3
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw8487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8487 raw8487Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw8487 raw8487Labels = mixedMoment B raw8487step0 raw8487step0Labels := by
      have hz : ∀ j, raw8487 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8487step0 = (fun i j => raw8487 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8487step0 raw8487; decide +kernel
      have hl : raw8487step0Labels = raw8487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8487 raw8487Labels permutation265 hz
    mixedMoment B raw8487step0 raw8487step0Labels = mixedMoment B raw8487step1 raw8487step1Labels := by
      have ha : raw8487step1 = (fun i j => raw8487step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8487step1 raw8487step0; decide +kernel
      have hl : raw8487step1Labels = raw8487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8487step0 raw8487step0Labels permutation32 permutation3
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw8488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8488 raw8488Labels = mixedMoment B node2644 node2644Labels := by
  calc
    mixedMoment B raw8488 raw8488Labels = mixedMoment B raw8488step0 raw8488step0Labels := by
      have hz : ∀ j, raw8488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8488step0 = (fun i j => raw8488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8488step0 raw8488; decide +kernel
      have hl : raw8488step0Labels = raw8488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8488 raw8488Labels permutation346 hz
    mixedMoment B raw8488step0 raw8488step0Labels = mixedMoment B raw8488step1 raw8488step1Labels := by
      have hz : ∀ j, raw8488step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8488step1 = (fun i j => raw8488step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8488step1 raw8488step0; decide +kernel
      have hl : raw8488step1Labels = raw8488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8488step0 raw8488step0Labels permutation56 hz
    mixedMoment B raw8488step1 raw8488step1Labels = mixedMoment B raw8488step2 raw8488step2Labels := by
      have ha : raw8488step2 = (fun i j => raw8488step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8488step2 raw8488step1; decide +kernel
      have hl : raw8488step2Labels = raw8488step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8488step1 raw8488step1Labels permutation8 permutation3
    _ = mixedMoment B node2644 node2644Labels := by rfl

def raw8489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8489 raw8489Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw8489 raw8489Labels = mixedMoment B raw8489step0 raw8489step0Labels := by
      have hz : ∀ j, raw8489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8489step0 = (fun i j => raw8489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8489step0 raw8489; decide +kernel
      have hl : raw8489step0Labels = raw8489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8489 raw8489Labels permutation346 hz
    mixedMoment B raw8489step0 raw8489step0Labels = mixedMoment B raw8489step1 raw8489step1Labels := by
      have hz : ∀ j, raw8489step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8489step1 = (fun i j => raw8489step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8489step1 raw8489step0; decide +kernel
      have hl : raw8489step1Labels = raw8489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8489step0 raw8489step0Labels permutation56 hz
    mixedMoment B raw8489step1 raw8489step1Labels = mixedMoment B raw8489step2 raw8489step2Labels := by
      have ha : raw8489step2 = (fun i j => raw8489step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8489step2 raw8489step1; decide +kernel
      have hl : raw8489step2Labels = raw8489step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8489step1 raw8489step1Labels permutation9 permutation3
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw8490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8490 raw8490Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw8490 raw8490Labels = mixedMoment B raw8490step0 raw8490step0Labels := by
      have hz : ∀ j, raw8490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8490step0 = (fun i j => raw8490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8490step0 raw8490; decide +kernel
      have hl : raw8490step0Labels = raw8490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8490 raw8490Labels permutation346 hz
    mixedMoment B raw8490step0 raw8490step0Labels = mixedMoment B raw8490step1 raw8490step1Labels := by
      have hz : ∀ j, raw8490step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8490step1 = (fun i j => raw8490step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8490step1 raw8490step0; decide +kernel
      have hl : raw8490step1Labels = raw8490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8490step0 raw8490step0Labels permutation56 hz
    mixedMoment B raw8490step1 raw8490step1Labels = mixedMoment B raw8490step2 raw8490step2Labels := by
      have ha : raw8490step2 = (fun i j => raw8490step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8490step2 raw8490step1; decide +kernel
      have hl : raw8490step2Labels = raw8490step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8490step1 raw8490step1Labels permutation8 permutation3
    _ = mixedMoment B node1055 node1055Labels := by rfl

def raw8491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8491 raw8491Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw8491 raw8491Labels = mixedMoment B raw8491step0 raw8491step0Labels := by
      have hz : ∀ j, raw8491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8491step0 = (fun i j => raw8491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8491step0 raw8491; decide +kernel
      have hl : raw8491step0Labels = raw8491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8491 raw8491Labels permutation346 hz
    mixedMoment B raw8491step0 raw8491step0Labels = mixedMoment B raw8491step1 raw8491step1Labels := by
      have ha : raw8491step1 = (fun i j => raw8491step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8491step1 raw8491step0; decide +kernel
      have hl : raw8491step1Labels = raw8491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8491step0 raw8491step0Labels permutation32 permutation3
    _ = mixedMoment B node2492 node2492Labels := by rfl

def raw8492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw8492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8492 raw8492Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw8492 raw8492Labels = mixedMoment B raw8492step0 raw8492step0Labels := by
      have hz : ∀ j, raw8492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8492step0 = (fun i j => raw8492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8492step0 raw8492; decide +kernel
      have hl : raw8492step0Labels = raw8492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8492 raw8492Labels permutation265 hz
    mixedMoment B raw8492step0 raw8492step0Labels = mixedMoment B raw8492step1 raw8492step1Labels := by
      have ha : raw8492step1 = (fun i j => raw8492step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8492step1 raw8492step0; decide +kernel
      have hl : raw8492step1Labels = raw8492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8492step0 raw8492step0Labels permutation32 permutation3
    _ = mixedMoment B node2492 node2492Labels := by rfl

def raw8493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw8493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8493 raw8493Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw8493 raw8493Labels = mixedMoment B raw8493step0 raw8493step0Labels := by
      have hz : ∀ j, raw8493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8493step0 = (fun i j => raw8493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8493step0 raw8493; decide +kernel
      have hl : raw8493step0Labels = raw8493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8493 raw8493Labels permutation346 hz
    mixedMoment B raw8493step0 raw8493step0Labels = mixedMoment B raw8493step1 raw8493step1Labels := by
      have hz : ∀ j, raw8493step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8493step1 = (fun i j => raw8493step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8493step1 raw8493step0; decide +kernel
      have hl : raw8493step1Labels = raw8493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8493step0 raw8493step0Labels permutation56 hz
    mixedMoment B raw8493step1 raw8493step1Labels = mixedMoment B raw8493step2 raw8493step2Labels := by
      have ha : raw8493step2 = (fun i j => raw8493step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8493step2 raw8493step1; decide +kernel
      have hl : raw8493step2Labels = raw8493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8493step1 raw8493step1Labels permutation8 permutation3
    _ = mixedMoment B node2635 node2635Labels := by rfl

def raw8494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw8494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8494 raw8494Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw8494 raw8494Labels = mixedMoment B raw8494step0 raw8494step0Labels := by
      have hz : ∀ j, raw8494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8494step0 = (fun i j => raw8494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8494step0 raw8494; decide +kernel
      have hl : raw8494step0Labels = raw8494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8494 raw8494Labels permutation346 hz
    mixedMoment B raw8494step0 raw8494step0Labels = mixedMoment B raw8494step1 raw8494step1Labels := by
      have hz : ∀ j, raw8494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8494step1 = (fun i j => raw8494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8494step1 raw8494step0; decide +kernel
      have hl : raw8494step1Labels = raw8494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8494step0 raw8494step0Labels permutation56 hz
    mixedMoment B raw8494step1 raw8494step1Labels = mixedMoment B raw8494step2 raw8494step2Labels := by
      have ha : raw8494step2 = (fun i j => raw8494step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8494step2 raw8494step1; decide +kernel
      have hl : raw8494step2Labels = raw8494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8494step1 raw8494step1Labels permutation10 permutation3
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw8495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8495step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8495 raw8495Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw8495 raw8495Labels = mixedMoment B raw8495step0 raw8495step0Labels := by
      have hz : ∀ j, raw8495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8495step0 = (fun i j => raw8495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8495step0 raw8495; decide +kernel
      have hl : raw8495step0Labels = raw8495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8495 raw8495Labels permutation346 hz
    mixedMoment B raw8495step0 raw8495step0Labels = mixedMoment B raw8495step1 raw8495step1Labels := by
      have ha : raw8495step1 = (fun i j => raw8495step0 (permutation124 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8495step1 raw8495step0; decide +kernel
      have hl : raw8495step1Labels = raw8495step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8495step0 raw8495step0Labels permutation124 permutation7
    mixedMoment B raw8495step1 raw8495step1Labels = mixedMoment B raw8495step2 raw8495step2Labels := by
      have ha : raw8495step2 = raw8495step1 := by apply Matrix.ext; unfold raw8495step2 raw8495step1; decide +kernel
      have hl : raw8495step1Labels = labelEmbedding1 ∘ raw8495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8495step1 raw8495step1Labels raw8495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw8496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8496step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8496 raw8496Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw8496 raw8496Labels = mixedMoment B raw8496step0 raw8496step0Labels := by
      have hz : ∀ j, raw8496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8496step0 = (fun i j => raw8496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8496step0 raw8496; decide +kernel
      have hl : raw8496step0Labels = raw8496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8496 raw8496Labels permutation265 hz
    mixedMoment B raw8496step0 raw8496step0Labels = mixedMoment B raw8496step1 raw8496step1Labels := by
      have ha : raw8496step1 = (fun i j => raw8496step0 (permutation124 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8496step1 raw8496step0; decide +kernel
      have hl : raw8496step1Labels = raw8496step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8496step0 raw8496step0Labels permutation124 permutation7
    mixedMoment B raw8496step1 raw8496step1Labels = mixedMoment B raw8496step2 raw8496step2Labels := by
      have ha : raw8496step2 = raw8496step1 := by apply Matrix.ext; unfold raw8496step2 raw8496step1; decide +kernel
      have hl : raw8496step1Labels = labelEmbedding1 ∘ raw8496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8496step1 raw8496step1Labels raw8496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw8497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8497step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8497step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8497 raw8497Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw8497 raw8497Labels = mixedMoment B raw8497step0 raw8497step0Labels := by
      have hz : ∀ j, raw8497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8497step0 = (fun i j => raw8497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8497step0 raw8497; decide +kernel
      have hl : raw8497step0Labels = raw8497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8497 raw8497Labels permutation346 hz
    mixedMoment B raw8497step0 raw8497step0Labels = mixedMoment B raw8497step1 raw8497step1Labels := by
      have hz : ∀ j, raw8497step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8497step1 = (fun i j => raw8497step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8497step1 raw8497step0; decide +kernel
      have hl : raw8497step1Labels = raw8497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8497step0 raw8497step0Labels permutation56 hz
    mixedMoment B raw8497step1 raw8497step1Labels = mixedMoment B raw8497step2 raw8497step2Labels := by
      have ha : raw8497step2 = (fun i j => raw8497step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8497step2 raw8497step1; decide +kernel
      have hl : raw8497step2Labels = raw8497step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8497step1 raw8497step1Labels permutation24 permutation7
    mixedMoment B raw8497step2 raw8497step2Labels = mixedMoment B raw8497step3 raw8497step3Labels := by
      have ha : raw8497step3 = raw8497step2 := by apply Matrix.ext; unfold raw8497step3 raw8497step2; decide +kernel
      have hl : raw8497step2Labels = labelEmbedding1 ∘ raw8497step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8497step2 raw8497step2Labels raw8497step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw8498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8498step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8498step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8498step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw8498step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8498 raw8498Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw8498 raw8498Labels = mixedMoment B raw8498step0 raw8498step0Labels := by
      have hz : ∀ j, raw8498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8498step0 = (fun i j => raw8498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8498step0 raw8498; decide +kernel
      have hl : raw8498step0Labels = raw8498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8498 raw8498Labels permutation346 hz
    mixedMoment B raw8498step0 raw8498step0Labels = mixedMoment B raw8498step1 raw8498step1Labels := by
      have hz : ∀ j, raw8498step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8498step1 = (fun i j => raw8498step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8498step1 raw8498step0; decide +kernel
      have hl : raw8498step1Labels = raw8498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8498step0 raw8498step0Labels permutation56 hz
    mixedMoment B raw8498step1 raw8498step1Labels = mixedMoment B raw8498step2 raw8498step2Labels := by
      have ha : raw8498step2 = (fun i j => raw8498step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8498step2 raw8498step1; decide +kernel
      have hl : raw8498step2Labels = raw8498step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8498step1 raw8498step1Labels permutation18 permutation5
    mixedMoment B raw8498step2 raw8498step2Labels = mixedMoment B raw8498step3 raw8498step3Labels := by
      have ha : raw8498step3 = raw8498step2 := by apply Matrix.ext; unfold raw8498step3 raw8498step2; decide +kernel
      have hl : raw8498step2Labels = labelEmbedding1 ∘ raw8498step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8498step2 raw8498step2Labels raw8498step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw8499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8499 raw8499Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw8499 raw8499Labels = mixedMoment B raw8499step0 raw8499step0Labels := by
      have hz : ∀ j, raw8499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8499step0 = (fun i j => raw8499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8499step0 raw8499; decide +kernel
      have hl : raw8499step0Labels = raw8499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8499 raw8499Labels permutation346 hz
    mixedMoment B raw8499step0 raw8499step0Labels = mixedMoment B raw8499step1 raw8499step1Labels := by
      have hz : ∀ j, raw8499step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8499step1 = (fun i j => raw8499step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8499step1 raw8499step0; decide +kernel
      have hl : raw8499step1Labels = raw8499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8499step0 raw8499step0Labels permutation56 hz
    mixedMoment B raw8499step1 raw8499step1Labels = mixedMoment B raw8499step2 raw8499step2Labels := by
      have ha : raw8499step2 = (fun i j => raw8499step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8499step2 raw8499step1; decide +kernel
      have hl : raw8499step2Labels = raw8499step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8499step1 raw8499step1Labels permutation24 permutation7
    mixedMoment B raw8499step2 raw8499step2Labels = mixedMoment B raw8499step3 raw8499step3Labels := by
      have ha : raw8499step3 = raw8499step2 := by apply Matrix.ext; unfold raw8499step3 raw8499step2; decide +kernel
      have hl : raw8499step2Labels = labelEmbedding1 ∘ raw8499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8499step2 raw8499step2Labels raw8499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw8500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8500 raw8500Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw8500 raw8500Labels = mixedMoment B raw8500step0 raw8500step0Labels := by
      have hz : ∀ j, raw8500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8500step0 = (fun i j => raw8500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8500step0 raw8500; decide +kernel
      have hl : raw8500step0Labels = raw8500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8500 raw8500Labels permutation346 hz
    mixedMoment B raw8500step0 raw8500step0Labels = mixedMoment B raw8500step1 raw8500step1Labels := by
      have ha : raw8500step1 = (fun i j => raw8500step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8500step1 raw8500step0; decide +kernel
      have hl : raw8500step1Labels = raw8500step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8500step0 raw8500step0Labels permutation45 permutation5
    mixedMoment B raw8500step1 raw8500step1Labels = mixedMoment B raw8500step2 raw8500step2Labels := by
      have ha : raw8500step2 = -raw8500step1 := by apply Matrix.ext; change ∀ i j, raw8500step2 i j = -(raw8500step1 i j); unfold raw8500step2 raw8500step1; decide +kernel
      have hl : raw8500step2Labels = raw8500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8500step2 raw8500step2Labels = mixedMoment B raw8500step3 raw8500step3Labels := by
      have ha : raw8500step3 = raw8500step2 := by apply Matrix.ext; unfold raw8500step3 raw8500step2; decide +kernel
      have hl : raw8500step2Labels = labelEmbedding1 ∘ raw8500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8500step2 raw8500step2Labels raw8500step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1649 node1649Labels := by rfl

def raw8501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8501 raw8501Labels = mixedMoment B node3447 node3447Labels := by
  calc
    mixedMoment B raw8501 raw8501Labels = mixedMoment B raw8501step0 raw8501step0Labels := by
      have ha : raw8501step0 = (fun i j => raw8501 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8501step0 raw8501; decide +kernel
      have hl : raw8501step0Labels = raw8501Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8501 raw8501Labels permutation189 permutation5
    mixedMoment B raw8501step0 raw8501step0Labels = mixedMoment B raw8501step1 raw8501step1Labels := by
      have ha : raw8501step1 = -raw8501step0 := by apply Matrix.ext; change ∀ i j, raw8501step1 i j = -(raw8501step0 i j); unfold raw8501step1 raw8501step0; decide +kernel
      have hl : raw8501step1Labels = raw8501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8501step1 raw8501step1Labels = mixedMoment B raw8501step2 raw8501step2Labels := by
      have ha : raw8501step2 = raw8501step1 := by apply Matrix.ext; unfold raw8501step2 raw8501step1; decide +kernel
      have hl : raw8501step1Labels = labelEmbedding1 ∘ raw8501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8501step1 raw8501step1Labels raw8501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3447 node3447Labels := by rfl

def raw8502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8502 raw8502Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw8502 raw8502Labels = mixedMoment B raw8502step0 raw8502step0Labels := by
      have hz : ∀ j, raw8502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8502step0 = (fun i j => raw8502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8502step0 raw8502; decide +kernel
      have hl : raw8502step0Labels = raw8502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8502 raw8502Labels permutation346 hz
    mixedMoment B raw8502step0 raw8502step0Labels = mixedMoment B raw8502step1 raw8502step1Labels := by
      have ha : raw8502step1 = (fun i j => raw8502step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8502step1 raw8502step0; decide +kernel
      have hl : raw8502step1Labels = raw8502step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8502step0 raw8502step0Labels permutation46 permutation5
    mixedMoment B raw8502step1 raw8502step1Labels = mixedMoment B raw8502step2 raw8502step2Labels := by
      have ha : raw8502step2 = -raw8502step1 := by apply Matrix.ext; change ∀ i j, raw8502step2 i j = -(raw8502step1 i j); unfold raw8502step2 raw8502step1; decide +kernel
      have hl : raw8502step2Labels = raw8502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8502step2 raw8502step2Labels = mixedMoment B raw8502step3 raw8502step3Labels := by
      have ha : raw8502step3 = raw8502step2 := by apply Matrix.ext; unfold raw8502step3 raw8502step2; decide +kernel
      have hl : raw8502step2Labels = labelEmbedding1 ∘ raw8502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8502step2 raw8502step2Labels raw8502step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw8503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8503 raw8503Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw8503 raw8503Labels = mixedMoment B raw8503step0 raw8503step0Labels := by
      have hz : ∀ j, raw8503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8503step0 = (fun i j => raw8503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8503step0 raw8503; decide +kernel
      have hl : raw8503step0Labels = raw8503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8503 raw8503Labels permutation346 hz
    mixedMoment B raw8503step0 raw8503step0Labels = mixedMoment B raw8503step1 raw8503step1Labels := by
      have ha : raw8503step1 = (fun i j => raw8503step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8503step1 raw8503step0; decide +kernel
      have hl : raw8503step1Labels = raw8503step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8503step0 raw8503step0Labels permutation45 permutation5
    mixedMoment B raw8503step1 raw8503step1Labels = mixedMoment B raw8503step2 raw8503step2Labels := by
      have ha : raw8503step2 = -raw8503step1 := by apply Matrix.ext; change ∀ i j, raw8503step2 i j = -(raw8503step1 i j); unfold raw8503step2 raw8503step1; decide +kernel
      have hl : raw8503step2Labels = raw8503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8503step2 raw8503step2Labels = mixedMoment B raw8503step3 raw8503step3Labels := by
      have ha : raw8503step3 = raw8503step2 := by apply Matrix.ext; unfold raw8503step3 raw8503step2; decide +kernel
      have hl : raw8503step2Labels = labelEmbedding1 ∘ raw8503step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8503step2 raw8503step2Labels raw8503step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw8504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8504step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8504 raw8504Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8504 raw8504Labels = mixedMoment B raw8504step0 raw8504step0Labels := by
      have hz : ∀ j, raw8504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8504step0 = (fun i j => raw8504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8504step0 raw8504; decide +kernel
      have hl : raw8504step0Labels = raw8504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8504 raw8504Labels permutation346 hz
    mixedMoment B raw8504step0 raw8504step0Labels = mixedMoment B raw8504step1 raw8504step1Labels := by
      have ha : raw8504step1 = (fun i j => raw8504step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8504step1 raw8504step0; decide +kernel
      have hl : raw8504step1Labels = raw8504step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8504step0 raw8504step0Labels permutation48 permutation5
    mixedMoment B raw8504step1 raw8504step1Labels = mixedMoment B raw8504step2 raw8504step2Labels := by
      have ha : raw8504step2 = -raw8504step1 := by apply Matrix.ext; change ∀ i j, raw8504step2 i j = -(raw8504step1 i j); unfold raw8504step2 raw8504step1; decide +kernel
      have hl : raw8504step2Labels = raw8504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8504step2 raw8504step2Labels = mixedMoment B raw8504step3 raw8504step3Labels := by
      have ha : raw8504step3 = raw8504step2 := by apply Matrix.ext; unfold raw8504step3 raw8504step2; decide +kernel
      have hl : raw8504step2Labels = labelEmbedding1 ∘ raw8504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8504step2 raw8504step2Labels raw8504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8505 raw8505Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw8505 raw8505Labels = mixedMoment B raw8505step0 raw8505step0Labels := by
      have hz : ∀ j, raw8505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8505step0 = (fun i j => raw8505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8505step0 raw8505; decide +kernel
      have hl : raw8505step0Labels = raw8505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8505 raw8505Labels permutation265 hz
    mixedMoment B raw8505step0 raw8505step0Labels = mixedMoment B raw8505step1 raw8505step1Labels := by
      have ha : raw8505step1 = (fun i j => raw8505step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8505step1 raw8505step0; decide +kernel
      have hl : raw8505step1Labels = raw8505step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8505step0 raw8505step0Labels permutation45 permutation5
    mixedMoment B raw8505step1 raw8505step1Labels = mixedMoment B raw8505step2 raw8505step2Labels := by
      have ha : raw8505step2 = -raw8505step1 := by apply Matrix.ext; change ∀ i j, raw8505step2 i j = -(raw8505step1 i j); unfold raw8505step2 raw8505step1; decide +kernel
      have hl : raw8505step2Labels = raw8505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8505step2 raw8505step2Labels = mixedMoment B raw8505step3 raw8505step3Labels := by
      have ha : raw8505step3 = raw8505step2 := by apply Matrix.ext; unfold raw8505step3 raw8505step2; decide +kernel
      have hl : raw8505step2Labels = labelEmbedding1 ∘ raw8505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8505step2 raw8505step2Labels raw8505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1649 node1649Labels := by rfl

def raw8506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8506 raw8506Labels = mixedMoment B node3447 node3447Labels := by
  calc
    mixedMoment B raw8506 raw8506Labels = mixedMoment B raw8506step0 raw8506step0Labels := by
      have ha : raw8506step0 = (fun i j => raw8506 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8506step0 raw8506; decide +kernel
      have hl : raw8506step0Labels = raw8506Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8506 raw8506Labels permutation165 permutation5
    mixedMoment B raw8506step0 raw8506step0Labels = mixedMoment B raw8506step1 raw8506step1Labels := by
      have ha : raw8506step1 = -raw8506step0 := by apply Matrix.ext; change ∀ i j, raw8506step1 i j = -(raw8506step0 i j); unfold raw8506step1 raw8506step0; decide +kernel
      have hl : raw8506step1Labels = raw8506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8506step1 raw8506step1Labels = mixedMoment B raw8506step2 raw8506step2Labels := by
      have ha : raw8506step2 = raw8506step1 := by apply Matrix.ext; unfold raw8506step2 raw8506step1; decide +kernel
      have hl : raw8506step1Labels = labelEmbedding1 ∘ raw8506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8506step1 raw8506step1Labels raw8506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3447 node3447Labels := by rfl

def raw8507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw8507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8507 raw8507Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw8507 raw8507Labels = mixedMoment B raw8507step0 raw8507step0Labels := by
      have hz : ∀ j, raw8507 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8507step0 = (fun i j => raw8507 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8507step0 raw8507; decide +kernel
      have hl : raw8507step0Labels = raw8507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8507 raw8507Labels permutation265 hz
    mixedMoment B raw8507step0 raw8507step0Labels = mixedMoment B raw8507step1 raw8507step1Labels := by
      have ha : raw8507step1 = (fun i j => raw8507step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8507step1 raw8507step0; decide +kernel
      have hl : raw8507step1Labels = raw8507step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8507step0 raw8507step0Labels permutation46 permutation5
    mixedMoment B raw8507step1 raw8507step1Labels = mixedMoment B raw8507step2 raw8507step2Labels := by
      have ha : raw8507step2 = -raw8507step1 := by apply Matrix.ext; change ∀ i j, raw8507step2 i j = -(raw8507step1 i j); unfold raw8507step2 raw8507step1; decide +kernel
      have hl : raw8507step2Labels = raw8507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8507step2 raw8507step2Labels = mixedMoment B raw8507step3 raw8507step3Labels := by
      have ha : raw8507step3 = raw8507step2 := by apply Matrix.ext; unfold raw8507step3 raw8507step2; decide +kernel
      have hl : raw8507step2Labels = labelEmbedding1 ∘ raw8507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8507step2 raw8507step2Labels raw8507step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw8508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8508step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8508step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8508step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8508 raw8508Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw8508 raw8508Labels = mixedMoment B raw8508step0 raw8508step0Labels := by
      have hz : ∀ j, raw8508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8508step0 = (fun i j => raw8508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8508step0 raw8508; decide +kernel
      have hl : raw8508step0Labels = raw8508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8508 raw8508Labels permutation265 hz
    mixedMoment B raw8508step0 raw8508step0Labels = mixedMoment B raw8508step1 raw8508step1Labels := by
      have ha : raw8508step1 = (fun i j => raw8508step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8508step1 raw8508step0; decide +kernel
      have hl : raw8508step1Labels = raw8508step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8508step0 raw8508step0Labels permutation45 permutation5
    mixedMoment B raw8508step1 raw8508step1Labels = mixedMoment B raw8508step2 raw8508step2Labels := by
      have ha : raw8508step2 = -raw8508step1 := by apply Matrix.ext; change ∀ i j, raw8508step2 i j = -(raw8508step1 i j); unfold raw8508step2 raw8508step1; decide +kernel
      have hl : raw8508step2Labels = raw8508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8508step2 raw8508step2Labels = mixedMoment B raw8508step3 raw8508step3Labels := by
      have ha : raw8508step3 = raw8508step2 := by apply Matrix.ext; unfold raw8508step3 raw8508step2; decide +kernel
      have hl : raw8508step2Labels = labelEmbedding1 ∘ raw8508step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8508step2 raw8508step2Labels raw8508step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw8509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8509step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8509 raw8509Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8509 raw8509Labels = mixedMoment B raw8509step0 raw8509step0Labels := by
      have hz : ∀ j, raw8509 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8509step0 = (fun i j => raw8509 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8509step0 raw8509; decide +kernel
      have hl : raw8509step0Labels = raw8509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8509 raw8509Labels permutation265 hz
    mixedMoment B raw8509step0 raw8509step0Labels = mixedMoment B raw8509step1 raw8509step1Labels := by
      have ha : raw8509step1 = (fun i j => raw8509step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8509step1 raw8509step0; decide +kernel
      have hl : raw8509step1Labels = raw8509step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8509step0 raw8509step0Labels permutation48 permutation5
    mixedMoment B raw8509step1 raw8509step1Labels = mixedMoment B raw8509step2 raw8509step2Labels := by
      have ha : raw8509step2 = -raw8509step1 := by apply Matrix.ext; change ∀ i j, raw8509step2 i j = -(raw8509step1 i j); unfold raw8509step2 raw8509step1; decide +kernel
      have hl : raw8509step2Labels = raw8509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8509step2 raw8509step2Labels = mixedMoment B raw8509step3 raw8509step3Labels := by
      have ha : raw8509step3 = raw8509step2 := by apply Matrix.ext; unfold raw8509step3 raw8509step2; decide +kernel
      have hl : raw8509step2Labels = labelEmbedding1 ∘ raw8509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8509step2 raw8509step2Labels raw8509step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8510step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8510step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8510step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8510step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8510 raw8510Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw8510 raw8510Labels = mixedMoment B raw8510step0 raw8510step0Labels := by
      have hz : ∀ j, raw8510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8510step0 = (fun i j => raw8510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8510step0 raw8510; decide +kernel
      have hl : raw8510step0Labels = raw8510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8510 raw8510Labels permutation346 hz
    mixedMoment B raw8510step0 raw8510step0Labels = mixedMoment B raw8510step1 raw8510step1Labels := by
      have hz : ∀ j, raw8510step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8510step1 = (fun i j => raw8510step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8510step1 raw8510step0; decide +kernel
      have hl : raw8510step1Labels = raw8510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8510step0 raw8510step0Labels permutation56 hz
    mixedMoment B raw8510step1 raw8510step1Labels = mixedMoment B raw8510step2 raw8510step2Labels := by
      have ha : raw8510step2 = (fun i j => raw8510step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8510step2 raw8510step1; decide +kernel
      have hl : raw8510step2Labels = raw8510step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8510step1 raw8510step1Labels permutation11 permutation5
    mixedMoment B raw8510step2 raw8510step2Labels = mixedMoment B raw8510step3 raw8510step3Labels := by
      have ha : raw8510step3 = -raw8510step2 := by apply Matrix.ext; change ∀ i j, raw8510step3 i j = -(raw8510step2 i j); unfold raw8510step3 raw8510step2; decide +kernel
      have hl : raw8510step3Labels = raw8510step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8510step3 raw8510step3Labels = mixedMoment B raw8510step4 raw8510step4Labels := by
      have ha : raw8510step4 = raw8510step3 := by apply Matrix.ext; unfold raw8510step4 raw8510step3; decide +kernel
      have hl : raw8510step3Labels = labelEmbedding1 ∘ raw8510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8510step3 raw8510step3Labels raw8510step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1651 node1651Labels := by rfl

def raw8511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8511 raw8511Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw8511 raw8511Labels = mixedMoment B raw8511step0 raw8511step0Labels := by
      have hz : ∀ j, raw8511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8511step0 = (fun i j => raw8511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8511step0 raw8511; decide +kernel
      have hl : raw8511step0Labels = raw8511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8511 raw8511Labels permutation346 hz
    mixedMoment B raw8511step0 raw8511step0Labels = mixedMoment B raw8511step1 raw8511step1Labels := by
      have ha : raw8511step1 = (fun i j => raw8511step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8511step1 raw8511step0; decide +kernel
      have hl : raw8511step1Labels = raw8511step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8511step0 raw8511step0Labels permutation103 permutation5
    mixedMoment B raw8511step1 raw8511step1Labels = mixedMoment B raw8511step2 raw8511step2Labels := by
      have ha : raw8511step2 = raw8511step1 := by apply Matrix.ext; unfold raw8511step2 raw8511step1; decide +kernel
      have hl : raw8511step1Labels = labelEmbedding1 ∘ raw8511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8511step1 raw8511step1Labels raw8511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw8512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8512 raw8512Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw8512 raw8512Labels = mixedMoment B raw8512step0 raw8512step0Labels := by
      have hz : ∀ j, raw8512 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8512step0 = (fun i j => raw8512 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8512step0 raw8512; decide +kernel
      have hl : raw8512step0Labels = raw8512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8512 raw8512Labels permutation265 hz
    mixedMoment B raw8512step0 raw8512step0Labels = mixedMoment B raw8512step1 raw8512step1Labels := by
      have ha : raw8512step1 = (fun i j => raw8512step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8512step1 raw8512step0; decide +kernel
      have hl : raw8512step1Labels = raw8512step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8512step0 raw8512step0Labels permutation103 permutation5
    mixedMoment B raw8512step1 raw8512step1Labels = mixedMoment B raw8512step2 raw8512step2Labels := by
      have ha : raw8512step2 = raw8512step1 := by apply Matrix.ext; unfold raw8512step2 raw8512step1; decide +kernel
      have hl : raw8512step1Labels = labelEmbedding1 ∘ raw8512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8512step1 raw8512step1Labels raw8512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw8513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8513step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8513step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8513 raw8513Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw8513 raw8513Labels = mixedMoment B raw8513step0 raw8513step0Labels := by
      have hz : ∀ j, raw8513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8513step0 = (fun i j => raw8513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8513step0 raw8513; decide +kernel
      have hl : raw8513step0Labels = raw8513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8513 raw8513Labels permutation346 hz
    mixedMoment B raw8513step0 raw8513step0Labels = mixedMoment B raw8513step1 raw8513step1Labels := by
      have hz : ∀ j, raw8513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8513step1 = (fun i j => raw8513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8513step1 raw8513step0; decide +kernel
      have hl : raw8513step1Labels = raw8513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8513step0 raw8513step0Labels permutation56 hz
    mixedMoment B raw8513step1 raw8513step1Labels = mixedMoment B raw8513step2 raw8513step2Labels := by
      have ha : raw8513step2 = (fun i j => raw8513step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8513step2 raw8513step1; decide +kernel
      have hl : raw8513step2Labels = raw8513step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8513step1 raw8513step1Labels permutation19 permutation5
    mixedMoment B raw8513step2 raw8513step2Labels = mixedMoment B raw8513step3 raw8513step3Labels := by
      have ha : raw8513step3 = raw8513step2 := by apply Matrix.ext; unfold raw8513step3 raw8513step2; decide +kernel
      have hl : raw8513step2Labels = labelEmbedding1 ∘ raw8513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8513step2 raw8513step2Labels raw8513step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw8514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8514step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8514 raw8514Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw8514 raw8514Labels = mixedMoment B raw8514step0 raw8514step0Labels := by
      have hz : ∀ j, raw8514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8514step0 = (fun i j => raw8514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8514step0 raw8514; decide +kernel
      have hl : raw8514step0Labels = raw8514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8514 raw8514Labels permutation346 hz
    mixedMoment B raw8514step0 raw8514step0Labels = mixedMoment B raw8514step1 raw8514step1Labels := by
      have hz : ∀ j, raw8514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8514step1 = (fun i j => raw8514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8514step1 raw8514step0; decide +kernel
      have hl : raw8514step1Labels = raw8514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8514step0 raw8514step0Labels permutation56 hz
    mixedMoment B raw8514step1 raw8514step1Labels = mixedMoment B raw8514step2 raw8514step2Labels := by
      have ha : raw8514step2 = (fun i j => raw8514step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8514step2 raw8514step1; decide +kernel
      have hl : raw8514step2Labels = raw8514step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8514step1 raw8514step1Labels permutation19 permutation5
    mixedMoment B raw8514step2 raw8514step2Labels = mixedMoment B raw8514step3 raw8514step3Labels := by
      have ha : raw8514step3 = raw8514step2 := by apply Matrix.ext; unfold raw8514step3 raw8514step2; decide +kernel
      have hl : raw8514step2Labels = labelEmbedding1 ∘ raw8514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8514step2 raw8514step2Labels raw8514step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw8515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8515step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8515step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8515step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8515step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8515step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8515 raw8515Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw8515 raw8515Labels = mixedMoment B raw8515step0 raw8515step0Labels := by
      have hz : ∀ j, raw8515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8515step0 = (fun i j => raw8515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8515step0 raw8515; decide +kernel
      have hl : raw8515step0Labels = raw8515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8515 raw8515Labels permutation346 hz
    mixedMoment B raw8515step0 raw8515step0Labels = mixedMoment B raw8515step1 raw8515step1Labels := by
      have hz : ∀ j, raw8515step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8515step1 = (fun i j => raw8515step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8515step1 raw8515step0; decide +kernel
      have hl : raw8515step1Labels = raw8515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8515step0 raw8515step0Labels permutation56 hz
    mixedMoment B raw8515step1 raw8515step1Labels = mixedMoment B raw8515step2 raw8515step2Labels := by
      have ha : raw8515step2 = (fun i j => raw8515step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8515step2 raw8515step1; decide +kernel
      have hl : raw8515step2Labels = raw8515step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8515step1 raw8515step1Labels permutation11 permutation5
    mixedMoment B raw8515step2 raw8515step2Labels = mixedMoment B raw8515step3 raw8515step3Labels := by
      have ha : raw8515step3 = -raw8515step2 := by apply Matrix.ext; change ∀ i j, raw8515step3 i j = -(raw8515step2 i j); unfold raw8515step3 raw8515step2; decide +kernel
      have hl : raw8515step3Labels = raw8515step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8515step3 raw8515step3Labels = mixedMoment B raw8515step4 raw8515step4Labels := by
      have ha : raw8515step4 = raw8515step3 := by apply Matrix.ext; unfold raw8515step4 raw8515step3; decide +kernel
      have hl : raw8515step3Labels = labelEmbedding1 ∘ raw8515step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8515step3 raw8515step3Labels raw8515step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw8516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8516step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8516step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8516 raw8516Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw8516 raw8516Labels = mixedMoment B raw8516step0 raw8516step0Labels := by
      have hz : ∀ j, raw8516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8516step0 = (fun i j => raw8516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8516step0 raw8516; decide +kernel
      have hl : raw8516step0Labels = raw8516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8516 raw8516Labels permutation346 hz
    mixedMoment B raw8516step0 raw8516step0Labels = mixedMoment B raw8516step1 raw8516step1Labels := by
      have ha : raw8516step1 = (fun i j => raw8516step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8516step1 raw8516step0; decide +kernel
      have hl : raw8516step1Labels = raw8516step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8516step0 raw8516step0Labels permutation35 permutation5
    mixedMoment B raw8516step1 raw8516step1Labels = mixedMoment B raw8516step2 raw8516step2Labels := by
      have ha : raw8516step2 = -raw8516step1 := by apply Matrix.ext; change ∀ i j, raw8516step2 i j = -(raw8516step1 i j); unfold raw8516step2 raw8516step1; decide +kernel
      have hl : raw8516step2Labels = raw8516step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8516step2 raw8516step2Labels = mixedMoment B raw8516step3 raw8516step3Labels := by
      have ha : raw8516step3 = raw8516step2 := by apply Matrix.ext; unfold raw8516step3 raw8516step2; decide +kernel
      have hl : raw8516step2Labels = labelEmbedding1 ∘ raw8516step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8516step2 raw8516step2Labels raw8516step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw8517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8517 raw8517Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw8517 raw8517Labels = mixedMoment B raw8517step0 raw8517step0Labels := by
      have hz : ∀ j, raw8517 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8517step0 = (fun i j => raw8517 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8517step0 raw8517; decide +kernel
      have hl : raw8517step0Labels = raw8517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8517 raw8517Labels permutation265 hz
    mixedMoment B raw8517step0 raw8517step0Labels = mixedMoment B raw8517step1 raw8517step1Labels := by
      have ha : raw8517step1 = (fun i j => raw8517step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8517step1 raw8517step0; decide +kernel
      have hl : raw8517step1Labels = raw8517step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8517step0 raw8517step0Labels permutation35 permutation5
    mixedMoment B raw8517step1 raw8517step1Labels = mixedMoment B raw8517step2 raw8517step2Labels := by
      have ha : raw8517step2 = -raw8517step1 := by apply Matrix.ext; change ∀ i j, raw8517step2 i j = -(raw8517step1 i j); unfold raw8517step2 raw8517step1; decide +kernel
      have hl : raw8517step2Labels = raw8517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8517step2 raw8517step2Labels = mixedMoment B raw8517step3 raw8517step3Labels := by
      have ha : raw8517step3 = raw8517step2 := by apply Matrix.ext; unfold raw8517step3 raw8517step2; decide +kernel
      have hl : raw8517step2Labels = labelEmbedding1 ∘ raw8517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8517step2 raw8517step2Labels raw8517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw8518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8518step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw8518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8518step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8518step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8518step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8518 raw8518Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw8518 raw8518Labels = mixedMoment B raw8518step0 raw8518step0Labels := by
      have hz : ∀ j, raw8518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8518step0 = (fun i j => raw8518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8518step0 raw8518; decide +kernel
      have hl : raw8518step0Labels = raw8518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8518 raw8518Labels permutation346 hz
    mixedMoment B raw8518step0 raw8518step0Labels = mixedMoment B raw8518step1 raw8518step1Labels := by
      have hz : ∀ j, raw8518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8518step1 = (fun i j => raw8518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8518step1 raw8518step0; decide +kernel
      have hl : raw8518step1Labels = raw8518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8518step0 raw8518step0Labels permutation56 hz
    mixedMoment B raw8518step1 raw8518step1Labels = mixedMoment B raw8518step2 raw8518step2Labels := by
      have ha : raw8518step2 = (fun i j => raw8518step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8518step2 raw8518step1; decide +kernel
      have hl : raw8518step2Labels = raw8518step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8518step1 raw8518step1Labels permutation10 permutation5
    mixedMoment B raw8518step2 raw8518step2Labels = mixedMoment B raw8518step3 raw8518step3Labels := by
      have ha : raw8518step3 = -raw8518step2 := by apply Matrix.ext; change ∀ i j, raw8518step3 i j = -(raw8518step2 i j); unfold raw8518step3 raw8518step2; decide +kernel
      have hl : raw8518step3Labels = raw8518step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8518step3 raw8518step3Labels = mixedMoment B raw8518step4 raw8518step4Labels := by
      have ha : raw8518step4 = raw8518step3 := by apply Matrix.ext; unfold raw8518step4 raw8518step3; decide +kernel
      have hl : raw8518step3Labels = labelEmbedding1 ∘ raw8518step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8518step3 raw8518step3Labels raw8518step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw8519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8519step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw8519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8519step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8519step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8519 raw8519Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw8519 raw8519Labels = mixedMoment B raw8519step0 raw8519step0Labels := by
      have hz : ∀ j, raw8519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8519step0 = (fun i j => raw8519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8519step0 raw8519; decide +kernel
      have hl : raw8519step0Labels = raw8519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8519 raw8519Labels permutation346 hz
    mixedMoment B raw8519step0 raw8519step0Labels = mixedMoment B raw8519step1 raw8519step1Labels := by
      have hz : ∀ j, raw8519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8519step1 = (fun i j => raw8519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8519step1 raw8519step0; decide +kernel
      have hl : raw8519step1Labels = raw8519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8519step0 raw8519step0Labels permutation56 hz
    mixedMoment B raw8519step1 raw8519step1Labels = mixedMoment B raw8519step2 raw8519step2Labels := by
      have ha : raw8519step2 = (fun i j => raw8519step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8519step2 raw8519step1; decide +kernel
      have hl : raw8519step2Labels = raw8519step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8519step1 raw8519step1Labels permutation13 permutation5
    mixedMoment B raw8519step2 raw8519step2Labels = mixedMoment B raw8519step3 raw8519step3Labels := by
      have ha : raw8519step3 = -raw8519step2 := by apply Matrix.ext; change ∀ i j, raw8519step3 i j = -(raw8519step2 i j); unfold raw8519step3 raw8519step2; decide +kernel
      have hl : raw8519step3Labels = raw8519step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8519step3 raw8519step3Labels = mixedMoment B raw8519step4 raw8519step4Labels := by
      have ha : raw8519step4 = raw8519step3 := by apply Matrix.ext; unfold raw8519step4 raw8519step3; decide +kernel
      have hl : raw8519step3Labels = labelEmbedding1 ∘ raw8519step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8519step3 raw8519step3Labels raw8519step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw8520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw8520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw8520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw8520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8520 raw8520Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw8520 raw8520Labels = mixedMoment B raw8520step0 raw8520step0Labels := by
      have hz : ∀ j, raw8520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8520step0 = (fun i j => raw8520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8520step0 raw8520; decide +kernel
      have hl : raw8520step0Labels = raw8520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8520 raw8520Labels permutation346 hz
    mixedMoment B raw8520step0 raw8520step0Labels = mixedMoment B raw8520step1 raw8520step1Labels := by
      have hz : ∀ j, raw8520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8520step1 = (fun i j => raw8520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8520step1 raw8520step0; decide +kernel
      have hl : raw8520step1Labels = raw8520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8520step0 raw8520step0Labels permutation56 hz
    mixedMoment B raw8520step1 raw8520step1Labels = mixedMoment B raw8520step2 raw8520step2Labels := by
      have ha : raw8520step2 = (fun i j => raw8520step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8520step2 raw8520step1; decide +kernel
      have hl : raw8520step2Labels = raw8520step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8520step1 raw8520step1Labels permutation10 permutation5
    mixedMoment B raw8520step2 raw8520step2Labels = mixedMoment B raw8520step3 raw8520step3Labels := by
      have ha : raw8520step3 = -raw8520step2 := by apply Matrix.ext; change ∀ i j, raw8520step3 i j = -(raw8520step2 i j); unfold raw8520step3 raw8520step2; decide +kernel
      have hl : raw8520step3Labels = raw8520step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8520step3 raw8520step3Labels = mixedMoment B raw8520step4 raw8520step4Labels := by
      have ha : raw8520step4 = raw8520step3 := by apply Matrix.ext; unfold raw8520step4 raw8520step3; decide +kernel
      have hl : raw8520step3Labels = labelEmbedding1 ∘ raw8520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8520step3 raw8520step3Labels raw8520step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1652 node1652Labels := by rfl

def raw8521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8521step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8521 raw8521Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw8521 raw8521Labels = mixedMoment B raw8521step0 raw8521step0Labels := by
      have hz : ∀ j, raw8521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8521step0 = (fun i j => raw8521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8521step0 raw8521; decide +kernel
      have hl : raw8521step0Labels = raw8521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8521 raw8521Labels permutation346 hz
    mixedMoment B raw8521step0 raw8521step0Labels = mixedMoment B raw8521step1 raw8521step1Labels := by
      have ha : raw8521step1 = (fun i j => raw8521step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8521step1 raw8521step0; decide +kernel
      have hl : raw8521step1Labels = raw8521step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8521step0 raw8521step0Labels permutation145 permutation5
    mixedMoment B raw8521step1 raw8521step1Labels = mixedMoment B raw8521step2 raw8521step2Labels := by
      have ha : raw8521step2 = raw8521step1 := by apply Matrix.ext; unfold raw8521step2 raw8521step1; decide +kernel
      have hl : raw8521step1Labels = labelEmbedding1 ∘ raw8521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8521step1 raw8521step1Labels raw8521step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3385 node3385Labels := by rfl

def raw8522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8522 raw8522Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw8522 raw8522Labels = mixedMoment B raw8522step0 raw8522step0Labels := by
      have hz : ∀ j, raw8522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8522step0 = (fun i j => raw8522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8522step0 raw8522; decide +kernel
      have hl : raw8522step0Labels = raw8522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8522 raw8522Labels permutation265 hz
    mixedMoment B raw8522step0 raw8522step0Labels = mixedMoment B raw8522step1 raw8522step1Labels := by
      have ha : raw8522step1 = (fun i j => raw8522step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8522step1 raw8522step0; decide +kernel
      have hl : raw8522step1Labels = raw8522step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8522step0 raw8522step0Labels permutation145 permutation5
    mixedMoment B raw8522step1 raw8522step1Labels = mixedMoment B raw8522step2 raw8522step2Labels := by
      have ha : raw8522step2 = raw8522step1 := by apply Matrix.ext; unfold raw8522step2 raw8522step1; decide +kernel
      have hl : raw8522step1Labels = labelEmbedding1 ∘ raw8522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8522step1 raw8522step1Labels raw8522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3385 node3385Labels := by rfl

def raw8523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8523 raw8523Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw8523 raw8523Labels = mixedMoment B raw8523step0 raw8523step0Labels := by
      have hz : ∀ j, raw8523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8523step0 = (fun i j => raw8523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8523step0 raw8523; decide +kernel
      have hl : raw8523step0Labels = raw8523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8523 raw8523Labels permutation346 hz
    mixedMoment B raw8523step0 raw8523step0Labels = mixedMoment B raw8523step1 raw8523step1Labels := by
      have hz : ∀ j, raw8523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8523step1 = (fun i j => raw8523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8523step1 raw8523step0; decide +kernel
      have hl : raw8523step1Labels = raw8523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8523step0 raw8523step0Labels permutation56 hz
    mixedMoment B raw8523step1 raw8523step1Labels = mixedMoment B raw8523step2 raw8523step2Labels := by
      have ha : raw8523step2 = (fun i j => raw8523step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8523step2 raw8523step1; decide +kernel
      have hl : raw8523step2Labels = raw8523step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8523step1 raw8523step1Labels permutation29 permutation5
    mixedMoment B raw8523step2 raw8523step2Labels = mixedMoment B raw8523step3 raw8523step3Labels := by
      have ha : raw8523step3 = raw8523step2 := by apply Matrix.ext; unfold raw8523step3 raw8523step2; decide +kernel
      have hl : raw8523step2Labels = labelEmbedding1 ∘ raw8523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8523step2 raw8523step2Labels raw8523step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

def raw8524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8524step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw8524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw8524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8524 raw8524Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw8524 raw8524Labels = mixedMoment B raw8524step0 raw8524step0Labels := by
      have hz : ∀ j, raw8524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8524step0 = (fun i j => raw8524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8524step0 raw8524; decide +kernel
      have hl : raw8524step0Labels = raw8524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8524 raw8524Labels permutation346 hz
    mixedMoment B raw8524step0 raw8524step0Labels = mixedMoment B raw8524step1 raw8524step1Labels := by
      have hz : ∀ j, raw8524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8524step1 = (fun i j => raw8524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8524step1 raw8524step0; decide +kernel
      have hl : raw8524step1Labels = raw8524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8524step0 raw8524step0Labels permutation56 hz
    mixedMoment B raw8524step1 raw8524step1Labels = mixedMoment B raw8524step2 raw8524step2Labels := by
      have ha : raw8524step2 = (fun i j => raw8524step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8524step2 raw8524step1; decide +kernel
      have hl : raw8524step2Labels = raw8524step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8524step1 raw8524step1Labels permutation29 permutation5
    mixedMoment B raw8524step2 raw8524step2Labels = mixedMoment B raw8524step3 raw8524step3Labels := by
      have ha : raw8524step3 = raw8524step2 := by apply Matrix.ext; unfold raw8524step3 raw8524step2; decide +kernel
      have hl : raw8524step2Labels = labelEmbedding1 ∘ raw8524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8524step2 raw8524step2Labels raw8524step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3396 node3396Labels := by rfl

def raw8525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8525 raw8525Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8525 raw8525Labels = mixedMoment B raw8525step0 raw8525step0Labels := by
      have hz : ∀ j, raw8525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8525step0 = (fun i j => raw8525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8525step0 raw8525; decide +kernel
      have hl : raw8525step0Labels = raw8525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525 raw8525Labels permutation346 hz
    mixedMoment B raw8525step0 raw8525step0Labels = mixedMoment B raw8525step1 raw8525step1Labels := by
      have hz : ∀ j, raw8525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8525step1 = (fun i j => raw8525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8525step1 raw8525step0; decide +kernel
      have hl : raw8525step1Labels = raw8525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525step0 raw8525step0Labels permutation56 hz
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw8526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8526 raw8526Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8526 raw8526Labels = mixedMoment B raw8526step0 raw8526step0Labels := by
      have hz : ∀ j, raw8526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8526step0 = (fun i j => raw8526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8526step0 raw8526; decide +kernel
      have hl : raw8526step0Labels = raw8526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8526 raw8526Labels permutation346 hz
    mixedMoment B raw8526step0 raw8526step0Labels = mixedMoment B raw8526step1 raw8526step1Labels := by
      have ha : raw8526step1 = (fun i j => raw8526step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8526step1 raw8526step0; decide +kernel
      have hl : raw8526step1Labels = raw8526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8526step0 raw8526step0Labels permutation98 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw8527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8527step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8527 raw8527Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8527 raw8527Labels = mixedMoment B raw8527step0 raw8527step0Labels := by
      have hz : ∀ j, raw8527 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8527step0 = (fun i j => raw8527 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8527step0 raw8527; decide +kernel
      have hl : raw8527step0Labels = raw8527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8527 raw8527Labels permutation265 hz
    mixedMoment B raw8527step0 raw8527step0Labels = mixedMoment B raw8527step1 raw8527step1Labels := by
      have ha : raw8527step1 = (fun i j => raw8527step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8527step1 raw8527step0; decide +kernel
      have hl : raw8527step1Labels = raw8527step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8527step0 raw8527step0Labels permutation98 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw8528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8528 raw8528Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw8528 raw8528Labels = mixedMoment B raw8528step0 raw8528step0Labels := by
      have hz : ∀ j, raw8528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8528step0 = (fun i j => raw8528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8528step0 raw8528; decide +kernel
      have hl : raw8528step0Labels = raw8528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528 raw8528Labels permutation346 hz
    mixedMoment B raw8528step0 raw8528step0Labels = mixedMoment B raw8528step1 raw8528step1Labels := by
      have hz : ∀ j, raw8528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8528step1 = (fun i j => raw8528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8528step1 raw8528step0; decide +kernel
      have hl : raw8528step1Labels = raw8528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528step0 raw8528step0Labels permutation56 hz
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw8529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8529 raw8529Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw8529 raw8529Labels = mixedMoment B raw8529step0 raw8529step0Labels := by
      have hz : ∀ j, raw8529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8529step0 = (fun i j => raw8529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8529step0 raw8529; decide +kernel
      have hl : raw8529step0Labels = raw8529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529 raw8529Labels permutation346 hz
    mixedMoment B raw8529step0 raw8529step0Labels = mixedMoment B raw8529step1 raw8529step1Labels := by
      have hz : ∀ j, raw8529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8529step1 = (fun i j => raw8529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8529step1 raw8529step0; decide +kernel
      have hl : raw8529step1Labels = raw8529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529step0 raw8529step0Labels permutation56 hz
    mixedMoment B raw8529step1 raw8529step1Labels = mixedMoment B raw8529step2 raw8529step2Labels := by
      have ha : raw8529step2 = (fun i j => raw8529step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8529step2 raw8529step1; decide +kernel
      have hl : raw8529step2Labels = raw8529step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8529step1 raw8529step1Labels permutation18 permutation4
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw8530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8530 raw8530Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8530 raw8530Labels = mixedMoment B raw8530step0 raw8530step0Labels := by
      have hz : ∀ j, raw8530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8530step0 = (fun i j => raw8530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8530step0 raw8530; decide +kernel
      have hl : raw8530step0Labels = raw8530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8530 raw8530Labels permutation346 hz
    mixedMoment B raw8530step0 raw8530step0Labels = mixedMoment B raw8530step1 raw8530step1Labels := by
      have hz : ∀ j, raw8530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8530step1 = (fun i j => raw8530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8530step1 raw8530step0; decide +kernel
      have hl : raw8530step1Labels = raw8530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8530step0 raw8530step0Labels permutation56 hz
    mixedMoment B raw8530step1 raw8530step1Labels = mixedMoment B raw8530step2 raw8530step2Labels := by
      have ha : raw8530step2 = (fun i j => raw8530step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8530step2 raw8530step1; decide +kernel
      have hl : raw8530step2Labels = raw8530step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8530step1 raw8530step1Labels permutation18 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw8531 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw8531step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8531step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8531step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical8531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8531 raw8531Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8531 raw8531Labels = mixedMoment B raw8531step0 raw8531step0Labels := by
      have hz : ∀ j, raw8531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8531step0 = (fun i j => raw8531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8531step0 raw8531; decide +kernel
      have hl : raw8531step0Labels = raw8531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531 raw8531Labels permutation346 hz
    mixedMoment B raw8531step0 raw8531step0Labels = mixedMoment B raw8531step1 raw8531step1Labels := by
      have hz : ∀ j, raw8531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8531step1 = (fun i j => raw8531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8531step1 raw8531step0; decide +kernel
      have hl : raw8531step1Labels = raw8531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531step0 raw8531step0Labels permutation56 hz
    mixedMoment B raw8531step1 raw8531step1Labels = mixedMoment B raw8531step2 raw8531step2Labels := by
      have ha : raw8531step2 = (fun i j => raw8531step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8531step2 raw8531step1; decide +kernel
      have hl : raw8531step2Labels = raw8531step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8531step1 raw8531step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw8532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8532 raw8532Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw8532 raw8532Labels = mixedMoment B raw8532step0 raw8532step0Labels := by
      have hz : ∀ j, raw8532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8532step0 = (fun i j => raw8532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8532step0 raw8532; decide +kernel
      have hl : raw8532step0Labels = raw8532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8532 raw8532Labels permutation346 hz
    mixedMoment B raw8532step0 raw8532step0Labels = mixedMoment B raw8532step1 raw8532step1Labels := by
      have ha : raw8532step1 = (fun i j => raw8532step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8532step1 raw8532step0; decide +kernel
      have hl : raw8532step1Labels = raw8532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8532step0 raw8532step0Labels permutation38 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

def raw8533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8533 raw8533Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw8533 raw8533Labels = mixedMoment B raw8533step0 raw8533step0Labels := by
      have hz : ∀ j, raw8533 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8533step0 = (fun i j => raw8533 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8533step0 raw8533; decide +kernel
      have hl : raw8533step0Labels = raw8533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8533 raw8533Labels permutation265 hz
    mixedMoment B raw8533step0 raw8533step0Labels = mixedMoment B raw8533step1 raw8533step1Labels := by
      have ha : raw8533step1 = (fun i j => raw8533step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8533step1 raw8533step0; decide +kernel
      have hl : raw8533step1Labels = raw8533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8533step0 raw8533step0Labels permutation38 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

def raw8534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8534 raw8534Labels = mixedMoment B node1437 node1437Labels := by
  calc
    mixedMoment B raw8534 raw8534Labels = mixedMoment B raw8534step0 raw8534step0Labels := by
      have hz : ∀ j, raw8534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8534step0 = (fun i j => raw8534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8534step0 raw8534; decide +kernel
      have hl : raw8534step0Labels = raw8534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8534 raw8534Labels permutation346 hz
    mixedMoment B raw8534step0 raw8534step0Labels = mixedMoment B raw8534step1 raw8534step1Labels := by
      have hz : ∀ j, raw8534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8534step1 = (fun i j => raw8534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8534step1 raw8534step0; decide +kernel
      have hl : raw8534step1Labels = raw8534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8534step0 raw8534step0Labels permutation56 hz
    _ = mixedMoment B node1437 node1437Labels := by rfl

def raw8535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8535 raw8535Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8535 raw8535Labels = mixedMoment B raw8535step0 raw8535step0Labels := by
      have hz : ∀ j, raw8535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8535step0 = (fun i j => raw8535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8535step0 raw8535; decide +kernel
      have hl : raw8535step0Labels = raw8535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535 raw8535Labels permutation346 hz
    mixedMoment B raw8535step0 raw8535step0Labels = mixedMoment B raw8535step1 raw8535step1Labels := by
      have hz : ∀ j, raw8535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8535step1 = (fun i j => raw8535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8535step1 raw8535step0; decide +kernel
      have hl : raw8535step1Labels = raw8535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535step0 raw8535step0Labels permutation56 hz
    mixedMoment B raw8535step1 raw8535step1Labels = mixedMoment B raw8535step2 raw8535step2Labels := by
      have ha : raw8535step2 = (fun i j => raw8535step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8535step2 raw8535step1; decide +kernel
      have hl : raw8535step2Labels = raw8535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8535step1 raw8535step1Labels permutation9 permutation2
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw8536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8536 raw8536Labels = mixedMoment B node1373 node1373Labels := by
  calc
    mixedMoment B raw8536 raw8536Labels = mixedMoment B raw8536step0 raw8536step0Labels := by
      have hz : ∀ j, raw8536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8536step0 = (fun i j => raw8536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8536step0 raw8536; decide +kernel
      have hl : raw8536step0Labels = raw8536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8536 raw8536Labels permutation346 hz
    mixedMoment B raw8536step0 raw8536step0Labels = mixedMoment B raw8536step1 raw8536step1Labels := by
      have hz : ∀ j, raw8536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8536step1 = (fun i j => raw8536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8536step1 raw8536step0; decide +kernel
      have hl : raw8536step1Labels = raw8536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8536step0 raw8536step0Labels permutation56 hz
    _ = mixedMoment B node1373 node1373Labels := by rfl

def raw8537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8537 raw8537Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw8537 raw8537Labels = mixedMoment B raw8537step0 raw8537step0Labels := by
      have ha : raw8537step0 = (fun i j => raw8537 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8537step0 raw8537; decide +kernel
      have hl : raw8537step0Labels = raw8537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8537 raw8537Labels permutation182 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

def raw8538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8538 raw8538Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8538 raw8538Labels = mixedMoment B raw8538step0 raw8538step0Labels := by
      have hz : ∀ j, raw8538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8538step0 = (fun i j => raw8538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8538step0 raw8538; decide +kernel
      have hl : raw8538step0Labels = raw8538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8538 raw8538Labels permutation346 hz
    mixedMoment B raw8538step0 raw8538step0Labels = mixedMoment B raw8538step1 raw8538step1Labels := by
      have ha : raw8538step1 = (fun i j => raw8538step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8538step1 raw8538step0; decide +kernel
      have hl : raw8538step1Labels = raw8538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8538step0 raw8538step0Labels permutation38 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw8539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8539step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8539 raw8539Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw8539 raw8539Labels = mixedMoment B raw8539step0 raw8539step0Labels := by
      have hz : ∀ j, raw8539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8539step0 = (fun i j => raw8539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8539step0 raw8539; decide +kernel
      have hl : raw8539step0Labels = raw8539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8539 raw8539Labels permutation346 hz
    mixedMoment B raw8539step0 raw8539step0Labels = mixedMoment B raw8539step1 raw8539step1Labels := by
      have ha : raw8539step1 = (fun i j => raw8539step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8539step1 raw8539step0; decide +kernel
      have hl : raw8539step1Labels = raw8539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8539step0 raw8539step0Labels permutation40 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw8540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw8540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8540 raw8540Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8540 raw8540Labels = mixedMoment B raw8540step0 raw8540step0Labels := by
      have hz : ∀ j, raw8540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8540step0 = (fun i j => raw8540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8540step0 raw8540; decide +kernel
      have hl : raw8540step0Labels = raw8540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8540 raw8540Labels permutation346 hz
    mixedMoment B raw8540step0 raw8540step0Labels = mixedMoment B raw8540step1 raw8540step1Labels := by
      have ha : raw8540step1 = (fun i j => raw8540step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8540step1 raw8540step0; decide +kernel
      have hl : raw8540step1Labels = raw8540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8540step0 raw8540step0Labels permutation39 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw8541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8541 raw8541Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw8541 raw8541Labels = mixedMoment B raw8541step0 raw8541step0Labels := by
      have ha : raw8541step0 = (fun i j => raw8541 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8541step0 raw8541; decide +kernel
      have hl : raw8541step0Labels = raw8541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8541 raw8541Labels permutation158 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

def raw8542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8542 raw8542Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8542 raw8542Labels = mixedMoment B raw8542step0 raw8542step0Labels := by
      have hz : ∀ j, raw8542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8542step0 = (fun i j => raw8542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8542step0 raw8542; decide +kernel
      have hl : raw8542step0Labels = raw8542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8542 raw8542Labels permutation346 hz
    mixedMoment B raw8542step0 raw8542step0Labels = mixedMoment B raw8542step1 raw8542step1Labels := by
      have ha : raw8542step1 = (fun i j => raw8542step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8542step1 raw8542step0; decide +kernel
      have hl : raw8542step1Labels = raw8542step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8542step0 raw8542step0Labels permutation101 permutation4
    _ = mixedMoment B node2639 node2639Labels := by rfl

def raw8543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8543 raw8543Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8543 raw8543Labels = mixedMoment B raw8543step0 raw8543step0Labels := by
      have hz : ∀ j, raw8543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8543step0 = (fun i j => raw8543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8543step0 raw8543; decide +kernel
      have hl : raw8543step0Labels = raw8543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8543 raw8543Labels permutation346 hz
    mixedMoment B raw8543step0 raw8543step0Labels = mixedMoment B raw8543step1 raw8543step1Labels := by
      have ha : raw8543step1 = (fun i j => raw8543step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8543step1 raw8543step0; decide +kernel
      have hl : raw8543step1Labels = raw8543step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8543step0 raw8543step0Labels permutation33 permutation2
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw8544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8544 raw8544Labels = mixedMoment B node2871 node2871Labels := by
  calc
    mixedMoment B raw8544 raw8544Labels = mixedMoment B raw8544step0 raw8544step0Labels := by
      have hz : ∀ j, raw8544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8544step0 = (fun i j => raw8544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8544step0 raw8544; decide +kernel
      have hl : raw8544step0Labels = raw8544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8544 raw8544Labels permutation346 hz
    mixedMoment B raw8544step0 raw8544step0Labels = mixedMoment B raw8544step1 raw8544step1Labels := by
      have ha : raw8544step1 = (fun i j => raw8544step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8544step1 raw8544step0; decide +kernel
      have hl : raw8544step1Labels = raw8544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8544step0 raw8544step0Labels permutation151 permutation2
    mixedMoment B raw8544step1 raw8544step1Labels = mixedMoment B raw8544step2 raw8544step2Labels := by
      have ha : raw8544step2 = -raw8544step1 := by apply Matrix.ext; change ∀ i j, raw8544step2 i j = -(raw8544step1 i j); unfold raw8544step2 raw8544step1; decide +kernel
      have hl : raw8544step2Labels = raw8544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2871 node2871Labels := by rfl

def raw8545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8545 raw8545Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8545 raw8545Labels = mixedMoment B raw8545step0 raw8545step0Labels := by
      have hz : ∀ j, raw8545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8545step0 = (fun i j => raw8545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8545step0 raw8545; decide +kernel
      have hl : raw8545step0Labels = raw8545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8545 raw8545Labels permutation265 hz
    mixedMoment B raw8545step0 raw8545step0Labels = mixedMoment B raw8545step1 raw8545step1Labels := by
      have ha : raw8545step1 = (fun i j => raw8545step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8545step1 raw8545step0; decide +kernel
      have hl : raw8545step1Labels = raw8545step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8545step0 raw8545step0Labels permutation38 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw8546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8546 raw8546Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw8546 raw8546Labels = mixedMoment B raw8546step0 raw8546step0Labels := by
      have hz : ∀ j, raw8546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8546step0 = (fun i j => raw8546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8546step0 raw8546; decide +kernel
      have hl : raw8546step0Labels = raw8546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546 raw8546Labels permutation346 hz
    mixedMoment B raw8546step0 raw8546step0Labels = mixedMoment B raw8546step1 raw8546step1Labels := by
      have hz : ∀ j, raw8546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8546step1 = (fun i j => raw8546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8546step1 raw8546step0; decide +kernel
      have hl : raw8546step1Labels = raw8546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8546step0 raw8546step0Labels permutation56 hz
    mixedMoment B raw8546step1 raw8546step1Labels = mixedMoment B raw8546step2 raw8546step2Labels := by
      have ha : raw8546step2 = (fun i j => raw8546step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8546step2 raw8546step1; decide +kernel
      have hl : raw8546step2Labels = raw8546step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8546step1 raw8546step1Labels permutation9 permutation2
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw8547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw8547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8547 raw8547Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw8547 raw8547Labels = mixedMoment B raw8547step0 raw8547step0Labels := by
      have hz : ∀ j, raw8547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8547step0 = (fun i j => raw8547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8547step0 raw8547; decide +kernel
      have hl : raw8547step0Labels = raw8547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8547 raw8547Labels permutation346 hz
    mixedMoment B raw8547step0 raw8547step0Labels = mixedMoment B raw8547step1 raw8547step1Labels := by
      have hz : ∀ j, raw8547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8547step1 = (fun i j => raw8547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8547step1 raw8547step0; decide +kernel
      have hl : raw8547step1Labels = raw8547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8547step0 raw8547step0Labels permutation56 hz
    _ = mixedMoment B node2886 node2886Labels := by rfl

def raw8548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw8548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8548 raw8548Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8548 raw8548Labels = mixedMoment B raw8548step0 raw8548step0Labels := by
      have hz : ∀ j, raw8548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8548step0 = (fun i j => raw8548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8548step0 raw8548; decide +kernel
      have hl : raw8548step0Labels = raw8548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8548 raw8548Labels permutation265 hz
    mixedMoment B raw8548step0 raw8548step0Labels = mixedMoment B raw8548step1 raw8548step1Labels := by
      have ha : raw8548step1 = (fun i j => raw8548step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8548step1 raw8548step0; decide +kernel
      have hl : raw8548step1Labels = raw8548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8548step0 raw8548step0Labels permutation33 permutation2
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw8549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw8549step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8549 raw8549Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8549 raw8549Labels = mixedMoment B raw8549step0 raw8549step0Labels := by
      have hz : ∀ j, raw8549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8549step0 = (fun i j => raw8549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8549step0 raw8549; decide +kernel
      have hl : raw8549step0Labels = raw8549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8549 raw8549Labels permutation346 hz
    mixedMoment B raw8549step0 raw8549step0Labels = mixedMoment B raw8549step1 raw8549step1Labels := by
      have hz : ∀ j, raw8549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8549step1 = (fun i j => raw8549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8549step1 raw8549step0; decide +kernel
      have hl : raw8549step1Labels = raw8549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8549step0 raw8549step0Labels permutation56 hz
    mixedMoment B raw8549step1 raw8549step1Labels = mixedMoment B raw8549step2 raw8549step2Labels := by
      have ha : raw8549step2 = (fun i j => raw8549step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8549step2 raw8549step1; decide +kernel
      have hl : raw8549step2Labels = raw8549step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8549step1 raw8549step1Labels permutation9 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8550 raw8550Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw8550 raw8550Labels = mixedMoment B raw8550step0 raw8550step0Labels := by
      have hz : ∀ j, raw8550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8550step0 = (fun i j => raw8550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8550step0 raw8550; decide +kernel
      have hl : raw8550step0Labels = raw8550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8550 raw8550Labels permutation265 hz
    mixedMoment B raw8550step0 raw8550step0Labels = mixedMoment B raw8550step1 raw8550step1Labels := by
      have ha : raw8550step1 = (fun i j => raw8550step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8550step1 raw8550step0; decide +kernel
      have hl : raw8550step1Labels = raw8550step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8550step0 raw8550step0Labels permutation40 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw8551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![2, -1, -1]]
def raw8551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8551 raw8551Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw8551 raw8551Labels = mixedMoment B raw8551step0 raw8551step0Labels := by
      have hz : ∀ j, raw8551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8551step0 = (fun i j => raw8551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8551step0 raw8551; decide +kernel
      have hl : raw8551step0Labels = raw8551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8551 raw8551Labels permutation346 hz
    mixedMoment B raw8551step0 raw8551step0Labels = mixedMoment B raw8551step1 raw8551step1Labels := by
      have hz : ∀ j, raw8551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8551step1 = (fun i j => raw8551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8551step1 raw8551step0; decide +kernel
      have hl : raw8551step1Labels = raw8551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8551step0 raw8551step0Labels permutation56 hz
    mixedMoment B raw8551step1 raw8551step1Labels = mixedMoment B raw8551step2 raw8551step2Labels := by
      have ha : raw8551step2 = (fun i j => raw8551step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8551step2 raw8551step1; decide +kernel
      have hl : raw8551step2Labels = raw8551step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8551step1 raw8551step1Labels permutation18 permutation4
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw8552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw8552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8552 raw8552Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw8552 raw8552Labels = mixedMoment B raw8552step0 raw8552step0Labels := by
      have hz : ∀ j, raw8552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8552step0 = (fun i j => raw8552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8552step0 raw8552; decide +kernel
      have hl : raw8552step0Labels = raw8552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8552 raw8552Labels permutation346 hz
    mixedMoment B raw8552step0 raw8552step0Labels = mixedMoment B raw8552step1 raw8552step1Labels := by
      have hz : ∀ j, raw8552step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8552step1 = (fun i j => raw8552step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8552step1 raw8552step0; decide +kernel
      have hl : raw8552step1Labels = raw8552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8552step0 raw8552step0Labels permutation56 hz
    _ = mixedMoment B node3046 node3046Labels := by rfl

def raw8553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8553step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8553 raw8553Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw8553 raw8553Labels = mixedMoment B raw8553step0 raw8553step0Labels := by
      have hz : ∀ j, raw8553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8553step0 = (fun i j => raw8553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8553step0 raw8553; decide +kernel
      have hl : raw8553step0Labels = raw8553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8553 raw8553Labels permutation265 hz
    mixedMoment B raw8553step0 raw8553step0Labels = mixedMoment B raw8553step1 raw8553step1Labels := by
      have ha : raw8553step1 = (fun i j => raw8553step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8553step1 raw8553step0; decide +kernel
      have hl : raw8553step1Labels = raw8553step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8553step0 raw8553step0Labels permutation38 permutation7
    mixedMoment B raw8553step1 raw8553step1Labels = mixedMoment B raw8553step2 raw8553step2Labels := by
      have ha : raw8553step2 = raw8553step1 := by apply Matrix.ext; unfold raw8553step2 raw8553step1; decide +kernel
      have hl : raw8553step1Labels = labelEmbedding10 ∘ raw8553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8553step1 raw8553step1Labels raw8553step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw8554 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8554step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8554step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8554step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8554 raw8554Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw8554 raw8554Labels = mixedMoment B raw8554step0 raw8554step0Labels := by
      have hz : ∀ j, raw8554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8554step0 = (fun i j => raw8554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8554step0 raw8554; decide +kernel
      have hl : raw8554step0Labels = raw8554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8554 raw8554Labels permutation346 hz
    mixedMoment B raw8554step0 raw8554step0Labels = mixedMoment B raw8554step1 raw8554step1Labels := by
      have hz : ∀ j, raw8554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8554step1 = (fun i j => raw8554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8554step1 raw8554step0; decide +kernel
      have hl : raw8554step1Labels = raw8554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8554step0 raw8554step0Labels permutation56 hz
    mixedMoment B raw8554step1 raw8554step1Labels = mixedMoment B raw8554step2 raw8554step2Labels := by
      have ha : raw8554step2 = (fun i j => raw8554step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8554step2 raw8554step1; decide +kernel
      have hl : raw8554step2Labels = raw8554step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8554step1 raw8554step1Labels permutation24 permutation3
    mixedMoment B raw8554step2 raw8554step2Labels = mixedMoment B raw8554step3 raw8554step3Labels := by
      have ha : raw8554step3 = raw8554step2 := by apply Matrix.ext; unfold raw8554step3 raw8554step2; decide +kernel
      have hl : raw8554step2Labels = labelEmbedding6 ∘ raw8554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8554step2 raw8554step2Labels raw8554step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw8555 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8555step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8555step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8555 raw8555Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw8555 raw8555Labels = mixedMoment B raw8555step0 raw8555step0Labels := by
      have hz : ∀ j, raw8555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8555step0 = (fun i j => raw8555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8555step0 raw8555; decide +kernel
      have hl : raw8555step0Labels = raw8555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8555 raw8555Labels permutation346 hz
    mixedMoment B raw8555step0 raw8555step0Labels = mixedMoment B raw8555step1 raw8555step1Labels := by
      have hz : ∀ j, raw8555step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8555step1 = (fun i j => raw8555step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8555step1 raw8555step0; decide +kernel
      have hl : raw8555step1Labels = raw8555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8555step0 raw8555step0Labels permutation56 hz
    mixedMoment B raw8555step1 raw8555step1Labels = mixedMoment B raw8555step2 raw8555step2Labels := by
      have ha : raw8555step2 = (fun i j => raw8555step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8555step2 raw8555step1; decide +kernel
      have hl : raw8555step2Labels = raw8555step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8555step1 raw8555step1Labels permutation8 permutation7
    mixedMoment B raw8555step2 raw8555step2Labels = mixedMoment B raw8555step3 raw8555step3Labels := by
      have ha : raw8555step3 = raw8555step2 := by apply Matrix.ext; unfold raw8555step3 raw8555step2; decide +kernel
      have hl : raw8555step2Labels = labelEmbedding10 ∘ raw8555step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8555step2 raw8555step2Labels raw8555step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw8556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8556step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8556step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8556step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8556step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8556 raw8556Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw8556 raw8556Labels = mixedMoment B raw8556step0 raw8556step0Labels := by
      have hz : ∀ j, raw8556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8556step0 = (fun i j => raw8556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8556step0 raw8556; decide +kernel
      have hl : raw8556step0Labels = raw8556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8556 raw8556Labels permutation346 hz
    mixedMoment B raw8556step0 raw8556step0Labels = mixedMoment B raw8556step1 raw8556step1Labels := by
      have ha : raw8556step1 = (fun i j => raw8556step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8556step1 raw8556step0; decide +kernel
      have hl : raw8556step1Labels = raw8556step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8556step0 raw8556step0Labels permutation45 permutation4
    mixedMoment B raw8556step1 raw8556step1Labels = mixedMoment B raw8556step2 raw8556step2Labels := by
      have ha : raw8556step2 = -raw8556step1 := by apply Matrix.ext; change ∀ i j, raw8556step2 i j = -(raw8556step1 i j); unfold raw8556step2 raw8556step1; decide +kernel
      have hl : raw8556step2Labels = raw8556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8556step2 raw8556step2Labels = mixedMoment B raw8556step3 raw8556step3Labels := by
      have ha : raw8556step3 = raw8556step2 := by apply Matrix.ext; unfold raw8556step3 raw8556step2; decide +kernel
      have hl : raw8556step2Labels = labelEmbedding7 ∘ raw8556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8556step2 raw8556step2Labels raw8556step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw8557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8557step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8557 raw8557Labels = mixedMoment B node5253 node5253Labels := by
  calc
    mixedMoment B raw8557 raw8557Labels = mixedMoment B raw8557step0 raw8557step0Labels := by
      have ha : raw8557step0 = (fun i j => raw8557 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8557step0 raw8557; decide +kernel
      have hl : raw8557step0Labels = raw8557Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8557 raw8557Labels permutation176 permutation6
    mixedMoment B raw8557step0 raw8557step0Labels = mixedMoment B raw8557step1 raw8557step1Labels := by
      have ha : raw8557step1 = raw8557step0 := by apply Matrix.ext; unfold raw8557step1 raw8557step0; decide +kernel
      have hl : raw8557step0Labels = labelEmbedding9 ∘ raw8557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8557step0 raw8557step0Labels raw8557step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5253 node5253Labels := by rfl

def raw8558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8558step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8558 raw8558Labels = mixedMoment B node5195 node5195Labels := by
  calc
    mixedMoment B raw8558 raw8558Labels = mixedMoment B raw8558step0 raw8558step0Labels := by
      have hz : ∀ j, raw8558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8558step0 = (fun i j => raw8558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8558step0 raw8558; decide +kernel
      have hl : raw8558step0Labels = raw8558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8558 raw8558Labels permutation346 hz
    mixedMoment B raw8558step0 raw8558step0Labels = mixedMoment B raw8558step1 raw8558step1Labels := by
      have ha : raw8558step1 = (fun i j => raw8558step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8558step1 raw8558step0; decide +kernel
      have hl : raw8558step1Labels = raw8558step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8558step0 raw8558step0Labels permutation122 permutation3
    mixedMoment B raw8558step1 raw8558step1Labels = mixedMoment B raw8558step2 raw8558step2Labels := by
      have ha : raw8558step2 = raw8558step1 := by apply Matrix.ext; unfold raw8558step2 raw8558step1; decide +kernel
      have hl : raw8558step1Labels = labelEmbedding6 ∘ raw8558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8558step1 raw8558step1Labels raw8558step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5195 node5195Labels := by rfl

def raw8559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8559step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8559 raw8559Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw8559 raw8559Labels = mixedMoment B raw8559step0 raw8559step0Labels := by
      have hz : ∀ j, raw8559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8559step0 = (fun i j => raw8559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8559step0 raw8559; decide +kernel
      have hl : raw8559step0Labels = raw8559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8559 raw8559Labels permutation346 hz
    mixedMoment B raw8559step0 raw8559step0Labels = mixedMoment B raw8559step1 raw8559step1Labels := by
      have ha : raw8559step1 = (fun i j => raw8559step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8559step1 raw8559step0; decide +kernel
      have hl : raw8559step1Labels = raw8559step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8559step0 raw8559step0Labels permutation32 permutation6
    mixedMoment B raw8559step1 raw8559step1Labels = mixedMoment B raw8559step2 raw8559step2Labels := by
      have ha : raw8559step2 = raw8559step1 := by apply Matrix.ext; unfold raw8559step2 raw8559step1; decide +kernel
      have hl : raw8559step1Labels = labelEmbedding9 ∘ raw8559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8559step1 raw8559step1Labels raw8559step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw8560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw8560step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8560step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8560step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8560 raw8560Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw8560 raw8560Labels = mixedMoment B raw8560step0 raw8560step0Labels := by
      have hz : ∀ j, raw8560 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8560step0 = (fun i j => raw8560 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8560step0 raw8560; decide +kernel
      have hl : raw8560step0Labels = raw8560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8560 raw8560Labels permutation265 hz
    mixedMoment B raw8560step0 raw8560step0Labels = mixedMoment B raw8560step1 raw8560step1Labels := by
      have ha : raw8560step1 = (fun i j => raw8560step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8560step1 raw8560step0; decide +kernel
      have hl : raw8560step1Labels = raw8560step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8560step0 raw8560step0Labels permutation45 permutation4
    mixedMoment B raw8560step1 raw8560step1Labels = mixedMoment B raw8560step2 raw8560step2Labels := by
      have ha : raw8560step2 = -raw8560step1 := by apply Matrix.ext; change ∀ i j, raw8560step2 i j = -(raw8560step1 i j); unfold raw8560step2 raw8560step1; decide +kernel
      have hl : raw8560step2Labels = raw8560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8560step2 raw8560step2Labels = mixedMoment B raw8560step3 raw8560step3Labels := by
      have ha : raw8560step3 = raw8560step2 := by apply Matrix.ext; unfold raw8560step3 raw8560step2; decide +kernel
      have hl : raw8560step2Labels = labelEmbedding7 ∘ raw8560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8560step2 raw8560step2Labels raw8560step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw8561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8561step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8561 raw8561Labels = mixedMoment B node5195 node5195Labels := by
  calc
    mixedMoment B raw8561 raw8561Labels = mixedMoment B raw8561step0 raw8561step0Labels := by
      have hz : ∀ j, raw8561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8561step0 = (fun i j => raw8561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8561step0 raw8561; decide +kernel
      have hl : raw8561step0Labels = raw8561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8561 raw8561Labels permutation265 hz
    mixedMoment B raw8561step0 raw8561step0Labels = mixedMoment B raw8561step1 raw8561step1Labels := by
      have ha : raw8561step1 = (fun i j => raw8561step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8561step1 raw8561step0; decide +kernel
      have hl : raw8561step1Labels = raw8561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8561step0 raw8561step0Labels permutation122 permutation3
    mixedMoment B raw8561step1 raw8561step1Labels = mixedMoment B raw8561step2 raw8561step2Labels := by
      have ha : raw8561step2 = raw8561step1 := by apply Matrix.ext; unfold raw8561step2 raw8561step1; decide +kernel
      have hl : raw8561step1Labels = labelEmbedding6 ∘ raw8561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8561step1 raw8561step1Labels raw8561step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5195 node5195Labels := by rfl

def raw8562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8562step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8562 raw8562Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw8562 raw8562Labels = mixedMoment B raw8562step0 raw8562step0Labels := by
      have hz : ∀ j, raw8562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8562step0 = (fun i j => raw8562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8562step0 raw8562; decide +kernel
      have hl : raw8562step0Labels = raw8562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8562 raw8562Labels permutation265 hz
    mixedMoment B raw8562step0 raw8562step0Labels = mixedMoment B raw8562step1 raw8562step1Labels := by
      have ha : raw8562step1 = (fun i j => raw8562step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8562step1 raw8562step0; decide +kernel
      have hl : raw8562step1Labels = raw8562step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8562step0 raw8562step0Labels permutation32 permutation6
    mixedMoment B raw8562step1 raw8562step1Labels = mixedMoment B raw8562step2 raw8562step2Labels := by
      have ha : raw8562step2 = raw8562step1 := by apply Matrix.ext; unfold raw8562step2 raw8562step1; decide +kernel
      have hl : raw8562step1Labels = labelEmbedding9 ∘ raw8562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8562step1 raw8562step1Labels raw8562step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw8563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw8563step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8563step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8563step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw8563step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8563 raw8563Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw8563 raw8563Labels = mixedMoment B raw8563step0 raw8563step0Labels := by
      have hz : ∀ j, raw8563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8563step0 = (fun i j => raw8563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8563step0 raw8563; decide +kernel
      have hl : raw8563step0Labels = raw8563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8563 raw8563Labels permutation346 hz
    mixedMoment B raw8563step0 raw8563step0Labels = mixedMoment B raw8563step1 raw8563step1Labels := by
      have hz : ∀ j, raw8563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8563step1 = (fun i j => raw8563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8563step1 raw8563step0; decide +kernel
      have hl : raw8563step1Labels = raw8563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8563step0 raw8563step0Labels permutation56 hz
    mixedMoment B raw8563step1 raw8563step1Labels = mixedMoment B raw8563step2 raw8563step2Labels := by
      have ha : raw8563step2 = (fun i j => raw8563step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8563step2 raw8563step1; decide +kernel
      have hl : raw8563step2Labels = raw8563step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8563step1 raw8563step1Labels permutation11 permutation4
    mixedMoment B raw8563step2 raw8563step2Labels = mixedMoment B raw8563step3 raw8563step3Labels := by
      have ha : raw8563step3 = -raw8563step2 := by apply Matrix.ext; change ∀ i j, raw8563step3 i j = -(raw8563step2 i j); unfold raw8563step3 raw8563step2; decide +kernel
      have hl : raw8563step3Labels = raw8563step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8563step3 raw8563step3Labels = mixedMoment B raw8563step4 raw8563step4Labels := by
      have ha : raw8563step4 = raw8563step3 := by apply Matrix.ext; unfold raw8563step4 raw8563step3; decide +kernel
      have hl : raw8563step3Labels = labelEmbedding7 ∘ raw8563step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8563step3 raw8563step3Labels raw8563step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw8564 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8564step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8564 raw8564Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw8564 raw8564Labels = mixedMoment B raw8564step0 raw8564step0Labels := by
      have hz : ∀ j, raw8564 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8564step0 = (fun i j => raw8564 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8564step0 raw8564; decide +kernel
      have hl : raw8564step0Labels = raw8564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8564 raw8564Labels permutation265 hz
    mixedMoment B raw8564step0 raw8564step0Labels = mixedMoment B raw8564step1 raw8564step1Labels := by
      have ha : raw8564step1 = (fun i j => raw8564step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8564step1 raw8564step0; decide +kernel
      have hl : raw8564step1Labels = raw8564step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8564step0 raw8564step0Labels permutation101 permutation5
    mixedMoment B raw8564step1 raw8564step1Labels = mixedMoment B raw8564step2 raw8564step2Labels := by
      have ha : raw8564step2 = raw8564step1 := by apply Matrix.ext; unfold raw8564step2 raw8564step1; decide +kernel
      have hl : raw8564step1Labels = labelEmbedding8 ∘ raw8564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8564step1 raw8564step1Labels raw8564step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

def raw8565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8565step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8565step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8565 raw8565Labels = mixedMoment B node4873 node4873Labels := by
  calc
    mixedMoment B raw8565 raw8565Labels = mixedMoment B raw8565step0 raw8565step0Labels := by
      have hz : ∀ j, raw8565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8565step0 = (fun i j => raw8565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8565step0 raw8565; decide +kernel
      have hl : raw8565step0Labels = raw8565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8565 raw8565Labels permutation346 hz
    mixedMoment B raw8565step0 raw8565step0Labels = mixedMoment B raw8565step1 raw8565step1Labels := by
      have hz : ∀ j, raw8565step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8565step1 = (fun i j => raw8565step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8565step1 raw8565step0; decide +kernel
      have hl : raw8565step1Labels = raw8565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8565step0 raw8565step0Labels permutation56 hz
    mixedMoment B raw8565step1 raw8565step1Labels = mixedMoment B raw8565step2 raw8565step2Labels := by
      have ha : raw8565step2 = (fun i j => raw8565step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8565step2 raw8565step1; decide +kernel
      have hl : raw8565step2Labels = raw8565step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8565step1 raw8565step1Labels permutation18 permutation5
    mixedMoment B raw8565step2 raw8565step2Labels = mixedMoment B raw8565step3 raw8565step3Labels := by
      have ha : raw8565step3 = raw8565step2 := by apply Matrix.ext; unfold raw8565step3 raw8565step2; decide +kernel
      have hl : raw8565step2Labels = labelEmbedding8 ∘ raw8565step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8565step2 raw8565step2Labels raw8565step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4873 node4873Labels := by rfl

def raw8566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8566step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8566step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8566step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8566 raw8566Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw8566 raw8566Labels = mixedMoment B raw8566step0 raw8566step0Labels := by
      have hz : ∀ j, raw8566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8566step0 = (fun i j => raw8566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8566step0 raw8566; decide +kernel
      have hl : raw8566step0Labels = raw8566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8566 raw8566Labels permutation346 hz
    mixedMoment B raw8566step0 raw8566step0Labels = mixedMoment B raw8566step1 raw8566step1Labels := by
      have hz : ∀ j, raw8566step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8566step1 = (fun i j => raw8566step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8566step1 raw8566step0; decide +kernel
      have hl : raw8566step1Labels = raw8566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8566step0 raw8566step0Labels permutation56 hz
    mixedMoment B raw8566step1 raw8566step1Labels = mixedMoment B raw8566step2 raw8566step2Labels := by
      have ha : raw8566step2 = (fun i j => raw8566step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8566step2 raw8566step1; decide +kernel
      have hl : raw8566step2Labels = raw8566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8566step1 raw8566step1Labels permutation15 permutation3
    mixedMoment B raw8566step2 raw8566step2Labels = mixedMoment B raw8566step3 raw8566step3Labels := by
      have ha : raw8566step3 = -raw8566step2 := by apply Matrix.ext; change ∀ i j, raw8566step3 i j = -(raw8566step2 i j); unfold raw8566step3 raw8566step2; decide +kernel
      have hl : raw8566step3Labels = raw8566step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8566step3 raw8566step3Labels = mixedMoment B raw8566step4 raw8566step4Labels := by
      have ha : raw8566step4 = raw8566step3 := by apply Matrix.ext; unfold raw8566step4 raw8566step3; decide +kernel
      have hl : raw8566step3Labels = labelEmbedding6 ∘ raw8566step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8566step3 raw8566step3Labels raw8566step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw8567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw8567step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8567step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8567step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw8567step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8567 raw8567Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw8567 raw8567Labels = mixedMoment B raw8567step0 raw8567step0Labels := by
      have hz : ∀ j, raw8567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8567step0 = (fun i j => raw8567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8567step0 raw8567; decide +kernel
      have hl : raw8567step0Labels = raw8567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8567 raw8567Labels permutation346 hz
    mixedMoment B raw8567step0 raw8567step0Labels = mixedMoment B raw8567step1 raw8567step1Labels := by
      have hz : ∀ j, raw8567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8567step1 = (fun i j => raw8567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8567step1 raw8567step0; decide +kernel
      have hl : raw8567step1Labels = raw8567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8567step0 raw8567step0Labels permutation56 hz
    mixedMoment B raw8567step1 raw8567step1Labels = mixedMoment B raw8567step2 raw8567step2Labels := by
      have ha : raw8567step2 = (fun i j => raw8567step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8567step2 raw8567step1; decide +kernel
      have hl : raw8567step2Labels = raw8567step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8567step1 raw8567step1Labels permutation10 permutation4
    mixedMoment B raw8567step2 raw8567step2Labels = mixedMoment B raw8567step3 raw8567step3Labels := by
      have ha : raw8567step3 = -raw8567step2 := by apply Matrix.ext; change ∀ i j, raw8567step3 i j = -(raw8567step2 i j); unfold raw8567step3 raw8567step2; decide +kernel
      have hl : raw8567step3Labels = raw8567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8567step3 raw8567step3Labels = mixedMoment B raw8567step4 raw8567step4Labels := by
      have ha : raw8567step4 = raw8567step3 := by apply Matrix.ext; unfold raw8567step4 raw8567step3; decide +kernel
      have hl : raw8567step3Labels = labelEmbedding7 ∘ raw8567step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8567step3 raw8567step3Labels raw8567step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw8568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw8568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw8568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8568 raw8568Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw8568 raw8568Labels = mixedMoment B raw8568step0 raw8568step0Labels := by
      have hz : ∀ j, raw8568 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8568step0 = (fun i j => raw8568 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8568step0 raw8568; decide +kernel
      have hl : raw8568step0Labels = raw8568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8568 raw8568Labels permutation265 hz
    mixedMoment B raw8568step0 raw8568step0Labels = mixedMoment B raw8568step1 raw8568step1Labels := by
      have ha : raw8568step1 = (fun i j => raw8568step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8568step1 raw8568step0; decide +kernel
      have hl : raw8568step1Labels = raw8568step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8568step0 raw8568step0Labels permutation32 permutation6
    mixedMoment B raw8568step1 raw8568step1Labels = mixedMoment B raw8568step2 raw8568step2Labels := by
      have ha : raw8568step2 = raw8568step1 := by apply Matrix.ext; unfold raw8568step2 raw8568step1; decide +kernel
      have hl : raw8568step1Labels = labelEmbedding9 ∘ raw8568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8568step1 raw8568step1Labels raw8568step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw8569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw8569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw8569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw8569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8569 raw8569Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw8569 raw8569Labels = mixedMoment B raw8569step0 raw8569step0Labels := by
      have hz : ∀ j, raw8569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8569step0 = (fun i j => raw8569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8569step0 raw8569; decide +kernel
      have hl : raw8569step0Labels = raw8569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8569 raw8569Labels permutation346 hz
    mixedMoment B raw8569step0 raw8569step0Labels = mixedMoment B raw8569step1 raw8569step1Labels := by
      have hz : ∀ j, raw8569step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8569step1 = (fun i j => raw8569step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8569step1 raw8569step0; decide +kernel
      have hl : raw8569step1Labels = raw8569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8569step0 raw8569step0Labels permutation56 hz
    mixedMoment B raw8569step1 raw8569step1Labels = mixedMoment B raw8569step2 raw8569step2Labels := by
      have ha : raw8569step2 = (fun i j => raw8569step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8569step2 raw8569step1; decide +kernel
      have hl : raw8569step2Labels = raw8569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8569step1 raw8569step1Labels permutation24 permutation3
    mixedMoment B raw8569step2 raw8569step2Labels = mixedMoment B raw8569step3 raw8569step3Labels := by
      have ha : raw8569step3 = raw8569step2 := by apply Matrix.ext; unfold raw8569step3 raw8569step2; decide +kernel
      have hl : raw8569step2Labels = labelEmbedding6 ∘ raw8569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8569step2 raw8569step2Labels raw8569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw8570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8570 raw8570Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw8570 raw8570Labels = mixedMoment B raw8570step0 raw8570step0Labels := by
      have hz : ∀ j, raw8570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8570step0 = (fun i j => raw8570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8570step0 raw8570; decide +kernel
      have hl : raw8570step0Labels = raw8570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8570 raw8570Labels permutation265 hz
    mixedMoment B raw8570step0 raw8570step0Labels = mixedMoment B raw8570step1 raw8570step1Labels := by
      have ha : raw8570step1 = (fun i j => raw8570step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8570step1 raw8570step0; decide +kernel
      have hl : raw8570step1Labels = raw8570step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8570step0 raw8570step0Labels permutation32 permutation6
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw8571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8571 raw8571Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw8571 raw8571Labels = mixedMoment B raw8571step0 raw8571step0Labels := by
      have hz : ∀ j, raw8571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8571step0 = (fun i j => raw8571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8571step0 raw8571; decide +kernel
      have hl : raw8571step0Labels = raw8571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8571 raw8571Labels permutation346 hz
    mixedMoment B raw8571step0 raw8571step0Labels = mixedMoment B raw8571step1 raw8571step1Labels := by
      have hz : ∀ j, raw8571step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8571step1 = (fun i j => raw8571step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8571step1 raw8571step0; decide +kernel
      have hl : raw8571step1Labels = raw8571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8571step0 raw8571step0Labels permutation56 hz
    mixedMoment B raw8571step1 raw8571step1Labels = mixedMoment B raw8571step2 raw8571step2Labels := by
      have ha : raw8571step2 = (fun i j => raw8571step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8571step2 raw8571step1; decide +kernel
      have hl : raw8571step2Labels = raw8571step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8571step1 raw8571step1Labels permutation24 permutation3
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw8572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw8572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw8572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8572 raw8572Labels = mixedMoment B node3117 node3117Labels := by
  calc
    mixedMoment B raw8572 raw8572Labels = mixedMoment B raw8572step0 raw8572step0Labels := by
      have hz : ∀ j, raw8572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8572step0 = (fun i j => raw8572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8572step0 raw8572; decide +kernel
      have hl : raw8572step0Labels = raw8572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8572 raw8572Labels permutation346 hz
    mixedMoment B raw8572step0 raw8572step0Labels = mixedMoment B raw8572step1 raw8572step1Labels := by
      have hz : ∀ j, raw8572step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8572step1 = (fun i j => raw8572step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8572step1 raw8572step0; decide +kernel
      have hl : raw8572step1Labels = raw8572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8572step0 raw8572step0Labels permutation56 hz
    mixedMoment B raw8572step1 raw8572step1Labels = mixedMoment B raw8572step2 raw8572step2Labels := by
      have ha : raw8572step2 = (fun i j => raw8572step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8572step2 raw8572step1; decide +kernel
      have hl : raw8572step2Labels = raw8572step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8572step1 raw8572step1Labels permutation8 permutation6
    _ = mixedMoment B node3117 node3117Labels := by rfl

def raw8573 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8573 raw8573Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw8573 raw8573Labels = mixedMoment B raw8573step0 raw8573step0Labels := by
      have hz : ∀ j, raw8573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8573step0 = (fun i j => raw8573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8573step0 raw8573; decide +kernel
      have hl : raw8573step0Labels = raw8573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8573 raw8573Labels permutation346 hz
    mixedMoment B raw8573step0 raw8573step0Labels = mixedMoment B raw8573step1 raw8573step1Labels := by
      have ha : raw8573step1 = (fun i j => raw8573step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8573step1 raw8573step0; decide +kernel
      have hl : raw8573step1Labels = raw8573step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8573step0 raw8573step0Labels permutation32 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw8574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw8574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8574 raw8574Labels = mixedMoment B node2713 node2713Labels := by
  calc
    mixedMoment B raw8574 raw8574Labels = mixedMoment B raw8574step0 raw8574step0Labels := by
      have ha : raw8574step0 = (fun i j => raw8574 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8574step0 raw8574; decide +kernel
      have hl : raw8574step0Labels = raw8574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8574 raw8574Labels permutation176 permutation6
    _ = mixedMoment B node2713 node2713Labels := by rfl

def raw8575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw8575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8575 raw8575Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw8575 raw8575Labels = mixedMoment B raw8575step0 raw8575step0Labels := by
      have hz : ∀ j, raw8575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8575step0 = (fun i j => raw8575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8575step0 raw8575; decide +kernel
      have hl : raw8575step0Labels = raw8575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8575 raw8575Labels permutation346 hz
    mixedMoment B raw8575step0 raw8575step0Labels = mixedMoment B raw8575step1 raw8575step1Labels := by
      have ha : raw8575step1 = (fun i j => raw8575step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8575step1 raw8575step0; decide +kernel
      have hl : raw8575step1Labels = raw8575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8575step0 raw8575step0Labels permutation122 permutation3
    _ = mixedMoment B node2629 node2629Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
