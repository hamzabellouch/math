import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7808 raw7808Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw7808 raw7808Labels = mixedMoment B raw7808step0 raw7808step0Labels := by
      have hz : ∀ j, raw7808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7808step0 = (fun i j => raw7808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7808step0 raw7808; decide +kernel
      have hl : raw7808step0Labels = raw7808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7808 raw7808Labels permutation346 hz
    mixedMoment B raw7808step0 raw7808step0Labels = mixedMoment B raw7808step1 raw7808step1Labels := by
      have hz : ∀ j, raw7808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7808step1 = (fun i j => raw7808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7808step1 raw7808step0; decide +kernel
      have hl : raw7808step1Labels = raw7808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7808step0 raw7808step0Labels permutation56 hz
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw7809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7809step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw7809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7809 raw7809Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw7809 raw7809Labels = mixedMoment B raw7809step0 raw7809step0Labels := by
      have hz : ∀ j, raw7809 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7809step0 = (fun i j => raw7809 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7809step0 raw7809; decide +kernel
      have hl : raw7809step0Labels = raw7809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7809 raw7809Labels permutation520 hz
    mixedMoment B raw7809step0 raw7809step0Labels = mixedMoment B raw7809step1 raw7809step1Labels := by
      have hz : ∀ j, raw7809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7809step1 = (fun i j => raw7809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7809step1 raw7809step0; decide +kernel
      have hl : raw7809step1Labels = raw7809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7809step0 raw7809step0Labels permutation80 hz
    mixedMoment B raw7809step1 raw7809step1Labels = mixedMoment B raw7809step2 raw7809step2Labels := by
      have hz : ∀ j, raw7809step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7809step2 = (fun i j => raw7809step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7809step2 raw7809step1; decide +kernel
      have hl : raw7809step2Labels = raw7809step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7809step1 raw7809step1Labels permutation14 hz
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw7810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7810 raw7810Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw7810 raw7810Labels = mixedMoment B raw7810step0 raw7810step0Labels := by
      have hz : ∀ j, raw7810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7810step0 = (fun i j => raw7810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7810step0 raw7810; decide +kernel
      have hl : raw7810step0Labels = raw7810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7810 raw7810Labels permutation346 hz
    mixedMoment B raw7810step0 raw7810step0Labels = mixedMoment B raw7810step1 raw7810step1Labels := by
      have hz : ∀ j, raw7810step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7810step1 = (fun i j => raw7810step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7810step1 raw7810step0; decide +kernel
      have hl : raw7810step1Labels = raw7810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7810step0 raw7810step0Labels permutation56 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw7811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7811step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7811 raw7811Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw7811 raw7811Labels = mixedMoment B raw7811step0 raw7811step0Labels := by
      have hz : ∀ j, raw7811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7811step0 = (fun i j => raw7811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7811step0 raw7811; decide +kernel
      have hl : raw7811step0Labels = raw7811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7811 raw7811Labels permutation346 hz
    mixedMoment B raw7811step0 raw7811step0Labels = mixedMoment B raw7811step1 raw7811step1Labels := by
      have ha : raw7811step1 = (fun i j => raw7811step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7811step1 raw7811step0; decide +kernel
      have hl : raw7811step1Labels = raw7811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7811step0 raw7811step0Labels permutation38 permutation3
    mixedMoment B raw7811step1 raw7811step1Labels = mixedMoment B raw7811step2 raw7811step2Labels := by
      have ha : raw7811step2 = raw7811step1 := by apply Matrix.ext; unfold raw7811step2 raw7811step1; decide +kernel
      have hl : raw7811step1Labels = labelEmbedding6 ∘ raw7811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7811step1 raw7811step1Labels raw7811step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw7812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7812 raw7812Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw7812 raw7812Labels = mixedMoment B raw7812step0 raw7812step0Labels := by
      have ha : raw7812step0 = (fun i j => raw7812 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7812step0 raw7812; decide +kernel
      have hl : raw7812step0Labels = raw7812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7812 raw7812Labels permutation182 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw7813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7813 raw7813Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw7813 raw7813Labels = mixedMoment B raw7813step0 raw7813step0Labels := by
      have hz : ∀ j, raw7813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7813step0 = (fun i j => raw7813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7813step0 raw7813; decide +kernel
      have hl : raw7813step0Labels = raw7813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7813 raw7813Labels permutation346 hz
    mixedMoment B raw7813step0 raw7813step0Labels = mixedMoment B raw7813step1 raw7813step1Labels := by
      have ha : raw7813step1 = (fun i j => raw7813step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7813step1 raw7813step0; decide +kernel
      have hl : raw7813step1Labels = raw7813step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7813step0 raw7813step0Labels permutation38 permutation2
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw7814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7814 raw7814Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7814 raw7814Labels = mixedMoment B raw7814step0 raw7814step0Labels := by
      have hz : ∀ j, raw7814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7814step0 = (fun i j => raw7814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7814step0 raw7814; decide +kernel
      have hl : raw7814step0Labels = raw7814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7814 raw7814Labels permutation520 hz
    mixedMoment B raw7814step0 raw7814step0Labels = mixedMoment B raw7814step1 raw7814step1Labels := by
      have hz : ∀ j, raw7814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7814step1 = (fun i j => raw7814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7814step1 raw7814step0; decide +kernel
      have hl : raw7814step1Labels = raw7814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7814step0 raw7814step0Labels permutation80 hz
    mixedMoment B raw7814step1 raw7814step1Labels = mixedMoment B raw7814step2 raw7814step2Labels := by
      have ha : raw7814step2 = (fun i j => raw7814step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7814step2 raw7814step1; decide +kernel
      have hl : raw7814step2Labels = raw7814step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7814step1 raw7814step1Labels permutation10 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw7815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7815 raw7815Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw7815 raw7815Labels = mixedMoment B raw7815step0 raw7815step0Labels := by
      have hz : ∀ j, raw7815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7815step0 = (fun i j => raw7815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7815step0 raw7815; decide +kernel
      have hl : raw7815step0Labels = raw7815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7815 raw7815Labels permutation346 hz
    mixedMoment B raw7815step0 raw7815step0Labels = mixedMoment B raw7815step1 raw7815step1Labels := by
      have ha : raw7815step1 = (fun i j => raw7815step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7815step1 raw7815step0; decide +kernel
      have hl : raw7815step1Labels = raw7815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7815step0 raw7815step0Labels permutation38 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw7816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7816step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7816 raw7816Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw7816 raw7816Labels = mixedMoment B raw7816step0 raw7816step0Labels := by
      have hz : ∀ j, raw7816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7816step0 = (fun i j => raw7816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7816step0 raw7816; decide +kernel
      have hl : raw7816step0Labels = raw7816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7816 raw7816Labels permutation265 hz
    mixedMoment B raw7816step0 raw7816step0Labels = mixedMoment B raw7816step1 raw7816step1Labels := by
      have ha : raw7816step1 = (fun i j => raw7816step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7816step1 raw7816step0; decide +kernel
      have hl : raw7816step1Labels = raw7816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7816step0 raw7816step0Labels permutation38 permutation3
    mixedMoment B raw7816step1 raw7816step1Labels = mixedMoment B raw7816step2 raw7816step2Labels := by
      have ha : raw7816step2 = raw7816step1 := by apply Matrix.ext; unfold raw7816step2 raw7816step1; decide +kernel
      have hl : raw7816step1Labels = labelEmbedding6 ∘ raw7816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7816step1 raw7816step1Labels raw7816step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw7817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7817 raw7817Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw7817 raw7817Labels = mixedMoment B raw7817step0 raw7817step0Labels := by
      have ha : raw7817step0 = (fun i j => raw7817 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7817step0 raw7817; decide +kernel
      have hl : raw7817step0Labels = raw7817Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7817 raw7817Labels permutation158 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw7818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7818 raw7818Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw7818 raw7818Labels = mixedMoment B raw7818step0 raw7818step0Labels := by
      have hz : ∀ j, raw7818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7818step0 = (fun i j => raw7818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7818step0 raw7818; decide +kernel
      have hl : raw7818step0Labels = raw7818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7818 raw7818Labels permutation265 hz
    mixedMoment B raw7818step0 raw7818step0Labels = mixedMoment B raw7818step1 raw7818step1Labels := by
      have ha : raw7818step1 = (fun i j => raw7818step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7818step1 raw7818step0; decide +kernel
      have hl : raw7818step1Labels = raw7818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7818step0 raw7818step0Labels permutation38 permutation2
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw7819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7819 raw7819Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7819 raw7819Labels = mixedMoment B raw7819step0 raw7819step0Labels := by
      have hz : ∀ j, raw7819 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7819step0 = (fun i j => raw7819 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7819step0 raw7819; decide +kernel
      have hl : raw7819step0Labels = raw7819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7819 raw7819Labels permutation520 hz
    mixedMoment B raw7819step0 raw7819step0Labels = mixedMoment B raw7819step1 raw7819step1Labels := by
      have hz : ∀ j, raw7819step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7819step1 = (fun i j => raw7819step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7819step1 raw7819step0; decide +kernel
      have hl : raw7819step1Labels = raw7819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7819step0 raw7819step0Labels permutation56 hz
    mixedMoment B raw7819step1 raw7819step1Labels = mixedMoment B raw7819step2 raw7819step2Labels := by
      have ha : raw7819step2 = (fun i j => raw7819step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7819step2 raw7819step1; decide +kernel
      have hl : raw7819step2Labels = raw7819step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7819step1 raw7819step1Labels permutation10 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw7820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7820 raw7820Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw7820 raw7820Labels = mixedMoment B raw7820step0 raw7820step0Labels := by
      have hz : ∀ j, raw7820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7820step0 = (fun i j => raw7820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7820step0 raw7820; decide +kernel
      have hl : raw7820step0Labels = raw7820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7820 raw7820Labels permutation265 hz
    mixedMoment B raw7820step0 raw7820step0Labels = mixedMoment B raw7820step1 raw7820step1Labels := by
      have ha : raw7820step1 = (fun i j => raw7820step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7820step1 raw7820step0; decide +kernel
      have hl : raw7820step1Labels = raw7820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7820step0 raw7820step0Labels permutation38 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw7821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7821 raw7821Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw7821 raw7821Labels = mixedMoment B raw7821step0 raw7821step0Labels := by
      have hz : ∀ j, raw7821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7821step0 = (fun i j => raw7821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7821step0 raw7821; decide +kernel
      have hl : raw7821step0Labels = raw7821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7821 raw7821Labels permutation346 hz
    mixedMoment B raw7821step0 raw7821step0Labels = mixedMoment B raw7821step1 raw7821step1Labels := by
      have hz : ∀ j, raw7821step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7821step1 = (fun i j => raw7821step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7821step1 raw7821step0; decide +kernel
      have hl : raw7821step1Labels = raw7821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7821step0 raw7821step0Labels permutation56 hz
    mixedMoment B raw7821step1 raw7821step1Labels = mixedMoment B raw7821step2 raw7821step2Labels := by
      have ha : raw7821step2 = (fun i j => raw7821step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7821step2 raw7821step1; decide +kernel
      have hl : raw7821step2Labels = raw7821step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7821step1 raw7821step1Labels permutation10 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw7822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7822 raw7822Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw7822 raw7822Labels = mixedMoment B raw7822step0 raw7822step0Labels := by
      have hz : ∀ j, raw7822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7822step0 = (fun i j => raw7822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7822step0 raw7822; decide +kernel
      have hl : raw7822step0Labels = raw7822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7822 raw7822Labels permutation346 hz
    mixedMoment B raw7822step0 raw7822step0Labels = mixedMoment B raw7822step1 raw7822step1Labels := by
      have ha : raw7822step1 = (fun i j => raw7822step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7822step1 raw7822step0; decide +kernel
      have hl : raw7822step1Labels = raw7822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7822step0 raw7822step0Labels permutation34 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw7823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7823 raw7823Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw7823 raw7823Labels = mixedMoment B raw7823step0 raw7823step0Labels := by
      have hz : ∀ j, raw7823 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7823step0 = (fun i j => raw7823 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7823step0 raw7823; decide +kernel
      have hl : raw7823step0Labels = raw7823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7823 raw7823Labels permutation265 hz
    mixedMoment B raw7823step0 raw7823step0Labels = mixedMoment B raw7823step1 raw7823step1Labels := by
      have ha : raw7823step1 = (fun i j => raw7823step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7823step1 raw7823step0; decide +kernel
      have hl : raw7823step1Labels = raw7823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7823step0 raw7823step0Labels permutation34 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw7824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7824step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7824 raw7824Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw7824 raw7824Labels = mixedMoment B raw7824step0 raw7824step0Labels := by
      have hz : ∀ j, raw7824 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7824step0 = (fun i j => raw7824 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7824step0 raw7824; decide +kernel
      have hl : raw7824step0Labels = raw7824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7824 raw7824Labels permutation520 hz
    mixedMoment B raw7824step0 raw7824step0Labels = mixedMoment B raw7824step1 raw7824step1Labels := by
      have hz : ∀ j, raw7824step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7824step1 = (fun i j => raw7824step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7824step1 raw7824step0; decide +kernel
      have hl : raw7824step1Labels = raw7824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7824step0 raw7824step0Labels permutation80 hz
    mixedMoment B raw7824step1 raw7824step1Labels = mixedMoment B raw7824step2 raw7824step2Labels := by
      have hz : ∀ j, raw7824step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7824step2 = (fun i j => raw7824step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7824step2 raw7824step1; decide +kernel
      have hl : raw7824step2Labels = raw7824step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7824step1 raw7824step1Labels permutation14 hz
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw7825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7825 raw7825Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw7825 raw7825Labels = mixedMoment B raw7825step0 raw7825step0Labels := by
      have hz : ∀ j, raw7825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7825step0 = (fun i j => raw7825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7825step0 raw7825; decide +kernel
      have hl : raw7825step0Labels = raw7825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7825 raw7825Labels permutation346 hz
    mixedMoment B raw7825step0 raw7825step0Labels = mixedMoment B raw7825step1 raw7825step1Labels := by
      have hz : ∀ j, raw7825step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7825step1 = (fun i j => raw7825step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7825step1 raw7825step0; decide +kernel
      have hl : raw7825step1Labels = raw7825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7825step0 raw7825step0Labels permutation56 hz
    mixedMoment B raw7825step1 raw7825step1Labels = mixedMoment B raw7825step2 raw7825step2Labels := by
      have ha : raw7825step2 = (fun i j => raw7825step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7825step2 raw7825step1; decide +kernel
      have hl : raw7825step2Labels = raw7825step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7825step1 raw7825step1Labels permutation10 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw7826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7826step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7826step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7826 raw7826Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw7826 raw7826Labels = mixedMoment B raw7826step0 raw7826step0Labels := by
      have hz : ∀ j, raw7826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7826step0 = (fun i j => raw7826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7826step0 raw7826; decide +kernel
      have hl : raw7826step0Labels = raw7826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7826 raw7826Labels permutation346 hz
    mixedMoment B raw7826step0 raw7826step0Labels = mixedMoment B raw7826step1 raw7826step1Labels := by
      have hz : ∀ j, raw7826step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7826step1 = (fun i j => raw7826step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7826step1 raw7826step0; decide +kernel
      have hl : raw7826step1Labels = raw7826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7826step0 raw7826step0Labels permutation56 hz
    mixedMoment B raw7826step1 raw7826step1Labels = mixedMoment B raw7826step2 raw7826step2Labels := by
      have ha : raw7826step2 = (fun i j => raw7826step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7826step2 raw7826step1; decide +kernel
      have hl : raw7826step2Labels = raw7826step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7826step1 raw7826step1Labels permutation9 permutation3
    mixedMoment B raw7826step2 raw7826step2Labels = mixedMoment B raw7826step3 raw7826step3Labels := by
      have ha : raw7826step3 = raw7826step2 := by apply Matrix.ext; unfold raw7826step3 raw7826step2; decide +kernel
      have hl : raw7826step2Labels = labelEmbedding6 ∘ raw7826step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7826step2 raw7826step2Labels raw7826step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw7827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7827 raw7827Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw7827 raw7827Labels = mixedMoment B raw7827step0 raw7827step0Labels := by
      have hz : ∀ j, raw7827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7827step0 = (fun i j => raw7827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7827step0 raw7827; decide +kernel
      have hl : raw7827step0Labels = raw7827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7827 raw7827Labels permutation346 hz
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw7828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7828 raw7828Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw7828 raw7828Labels = mixedMoment B raw7828step0 raw7828step0Labels := by
      have hz : ∀ j, raw7828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7828step0 = (fun i j => raw7828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7828step0 raw7828; decide +kernel
      have hl : raw7828step0Labels = raw7828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7828 raw7828Labels permutation265 hz
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw7829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7829 raw7829Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw7829 raw7829Labels = mixedMoment B raw7829step0 raw7829step0Labels := by
      have hz : ∀ j, raw7829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7829step0 = (fun i j => raw7829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7829step0 raw7829; decide +kernel
      have hl : raw7829step0Labels = raw7829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7829 raw7829Labels permutation346 hz
    mixedMoment B raw7829step0 raw7829step0Labels = mixedMoment B raw7829step1 raw7829step1Labels := by
      have hz : ∀ j, raw7829step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7829step1 = (fun i j => raw7829step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7829step1 raw7829step0; decide +kernel
      have hl : raw7829step1Labels = raw7829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7829step0 raw7829step0Labels permutation56 hz
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw7830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7830 raw7830Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw7830 raw7830Labels = mixedMoment B raw7830step0 raw7830step0Labels := by
      have hz : ∀ j, raw7830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7830step0 = (fun i j => raw7830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7830step0 raw7830; decide +kernel
      have hl : raw7830step0Labels = raw7830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7830 raw7830Labels permutation346 hz
    mixedMoment B raw7830step0 raw7830step0Labels = mixedMoment B raw7830step1 raw7830step1Labels := by
      have hz : ∀ j, raw7830step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7830step1 = (fun i j => raw7830step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7830step1 raw7830step0; decide +kernel
      have hl : raw7830step1Labels = raw7830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7830step0 raw7830step0Labels permutation56 hz
    mixedMoment B raw7830step1 raw7830step1Labels = mixedMoment B raw7830step2 raw7830step2Labels := by
      have ha : raw7830step2 = (fun i j => raw7830step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7830step2 raw7830step1; decide +kernel
      have hl : raw7830step2Labels = raw7830step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7830step1 raw7830step1Labels permutation9 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw7831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7831step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7831 raw7831Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw7831 raw7831Labels = mixedMoment B raw7831step0 raw7831step0Labels := by
      have hz : ∀ j, raw7831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7831step0 = (fun i j => raw7831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7831step0 raw7831; decide +kernel
      have hl : raw7831step0Labels = raw7831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7831 raw7831Labels permutation346 hz
    mixedMoment B raw7831step0 raw7831step0Labels = mixedMoment B raw7831step1 raw7831step1Labels := by
      have hz : ∀ j, raw7831step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7831step1 = (fun i j => raw7831step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7831step1 raw7831step0; decide +kernel
      have hl : raw7831step1Labels = raw7831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7831step0 raw7831step0Labels permutation56 hz
    mixedMoment B raw7831step1 raw7831step1Labels = mixedMoment B raw7831step2 raw7831step2Labels := by
      have ha : raw7831step2 = (fun i j => raw7831step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7831step2 raw7831step1; decide +kernel
      have hl : raw7831step2Labels = raw7831step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7831step1 raw7831step1Labels permutation8 permutation3
    mixedMoment B raw7831step2 raw7831step2Labels = mixedMoment B raw7831step3 raw7831step3Labels := by
      have ha : raw7831step3 = raw7831step2 := by apply Matrix.ext; unfold raw7831step3 raw7831step2; decide +kernel
      have hl : raw7831step2Labels = labelEmbedding6 ∘ raw7831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7831step2 raw7831step2Labels raw7831step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw7832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7832step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7832step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7832step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7832step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7832 raw7832Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw7832 raw7832Labels = mixedMoment B raw7832step0 raw7832step0Labels := by
      have hz : ∀ j, raw7832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7832step0 = (fun i j => raw7832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7832step0 raw7832; decide +kernel
      have hl : raw7832step0Labels = raw7832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7832 raw7832Labels permutation346 hz
    mixedMoment B raw7832step0 raw7832step0Labels = mixedMoment B raw7832step1 raw7832step1Labels := by
      have ha : raw7832step1 = (fun i j => raw7832step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7832step1 raw7832step0; decide +kernel
      have hl : raw7832step1Labels = raw7832step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7832step0 raw7832step0Labels permutation151 permutation3
    mixedMoment B raw7832step1 raw7832step1Labels = mixedMoment B raw7832step2 raw7832step2Labels := by
      have ha : raw7832step2 = -raw7832step1 := by apply Matrix.ext; change ∀ i j, raw7832step2 i j = -(raw7832step1 i j); unfold raw7832step2 raw7832step1; decide +kernel
      have hl : raw7832step2Labels = raw7832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7832step2 raw7832step2Labels = mixedMoment B raw7832step3 raw7832step3Labels := by
      have ha : raw7832step3 = raw7832step2 := by apply Matrix.ext; unfold raw7832step3 raw7832step2; decide +kernel
      have hl : raw7832step2Labels = labelEmbedding6 ∘ raw7832step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7832step2 raw7832step2Labels raw7832step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw7833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7833step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7833step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7833step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7833step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7833 raw7833Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw7833 raw7833Labels = mixedMoment B raw7833step0 raw7833step0Labels := by
      have hz : ∀ j, raw7833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7833step0 = (fun i j => raw7833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7833step0 raw7833; decide +kernel
      have hl : raw7833step0Labels = raw7833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7833 raw7833Labels permutation265 hz
    mixedMoment B raw7833step0 raw7833step0Labels = mixedMoment B raw7833step1 raw7833step1Labels := by
      have ha : raw7833step1 = (fun i j => raw7833step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7833step1 raw7833step0; decide +kernel
      have hl : raw7833step1Labels = raw7833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7833step0 raw7833step0Labels permutation151 permutation3
    mixedMoment B raw7833step1 raw7833step1Labels = mixedMoment B raw7833step2 raw7833step2Labels := by
      have ha : raw7833step2 = -raw7833step1 := by apply Matrix.ext; change ∀ i j, raw7833step2 i j = -(raw7833step1 i j); unfold raw7833step2 raw7833step1; decide +kernel
      have hl : raw7833step2Labels = raw7833step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7833step2 raw7833step2Labels = mixedMoment B raw7833step3 raw7833step3Labels := by
      have ha : raw7833step3 = raw7833step2 := by apply Matrix.ext; unfold raw7833step3 raw7833step2; decide +kernel
      have hl : raw7833step2Labels = labelEmbedding6 ∘ raw7833step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7833step2 raw7833step2Labels raw7833step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw7834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7834step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7834step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7834step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7834 raw7834Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw7834 raw7834Labels = mixedMoment B raw7834step0 raw7834step0Labels := by
      have hz : ∀ j, raw7834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7834step0 = (fun i j => raw7834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7834step0 raw7834; decide +kernel
      have hl : raw7834step0Labels = raw7834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7834 raw7834Labels permutation346 hz
    mixedMoment B raw7834step0 raw7834step0Labels = mixedMoment B raw7834step1 raw7834step1Labels := by
      have hz : ∀ j, raw7834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7834step1 = (fun i j => raw7834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7834step1 raw7834step0; decide +kernel
      have hl : raw7834step1Labels = raw7834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7834step0 raw7834step0Labels permutation56 hz
    mixedMoment B raw7834step1 raw7834step1Labels = mixedMoment B raw7834step2 raw7834step2Labels := by
      have ha : raw7834step2 = (fun i j => raw7834step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7834step2 raw7834step1; decide +kernel
      have hl : raw7834step2Labels = raw7834step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7834step1 raw7834step1Labels permutation31 permutation3
    mixedMoment B raw7834step2 raw7834step2Labels = mixedMoment B raw7834step3 raw7834step3Labels := by
      have ha : raw7834step3 = -raw7834step2 := by apply Matrix.ext; change ∀ i j, raw7834step3 i j = -(raw7834step2 i j); unfold raw7834step3 raw7834step2; decide +kernel
      have hl : raw7834step3Labels = raw7834step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7834step3 raw7834step3Labels = mixedMoment B raw7834step4 raw7834step4Labels := by
      have ha : raw7834step4 = raw7834step3 := by apply Matrix.ext; unfold raw7834step4 raw7834step3; decide +kernel
      have hl : raw7834step3Labels = labelEmbedding6 ∘ raw7834step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7834step3 raw7834step3Labels raw7834step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw7835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7835step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7835 raw7835Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw7835 raw7835Labels = mixedMoment B raw7835step0 raw7835step0Labels := by
      have hz : ∀ j, raw7835 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7835step0 = (fun i j => raw7835 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7835step0 raw7835; decide +kernel
      have hl : raw7835step0Labels = raw7835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835 raw7835Labels permutation520 hz
    mixedMoment B raw7835step0 raw7835step0Labels = mixedMoment B raw7835step1 raw7835step1Labels := by
      have hz : ∀ j, raw7835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7835step1 = (fun i j => raw7835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7835step1 raw7835step0; decide +kernel
      have hl : raw7835step1Labels = raw7835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835step0 raw7835step0Labels permutation80 hz
    mixedMoment B raw7835step1 raw7835step1Labels = mixedMoment B raw7835step2 raw7835step2Labels := by
      have hz : ∀ j, raw7835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7835step2 = (fun i j => raw7835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7835step2 raw7835step1; decide +kernel
      have hl : raw7835step2Labels = raw7835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7835step1 raw7835step1Labels permutation14 hz
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw7836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7836 raw7836Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw7836 raw7836Labels = mixedMoment B raw7836step0 raw7836step0Labels := by
      have hz : ∀ j, raw7836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7836step0 = (fun i j => raw7836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7836step0 raw7836; decide +kernel
      have hl : raw7836step0Labels = raw7836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7836 raw7836Labels permutation346 hz
    mixedMoment B raw7836step0 raw7836step0Labels = mixedMoment B raw7836step1 raw7836step1Labels := by
      have ha : raw7836step1 = (fun i j => raw7836step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7836step1 raw7836step0; decide +kernel
      have hl : raw7836step1Labels = raw7836step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7836step0 raw7836step0Labels permutation151 permutation3
    mixedMoment B raw7836step1 raw7836step1Labels = mixedMoment B raw7836step2 raw7836step2Labels := by
      have ha : raw7836step2 = -raw7836step1 := by apply Matrix.ext; change ∀ i j, raw7836step2 i j = -(raw7836step1 i j); unfold raw7836step2 raw7836step1; decide +kernel
      have hl : raw7836step2Labels = raw7836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw7837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7837 raw7837Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw7837 raw7837Labels = mixedMoment B raw7837step0 raw7837step0Labels := by
      have hz : ∀ j, raw7837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7837step0 = (fun i j => raw7837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7837step0 raw7837; decide +kernel
      have hl : raw7837step0Labels = raw7837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7837 raw7837Labels permutation265 hz
    mixedMoment B raw7837step0 raw7837step0Labels = mixedMoment B raw7837step1 raw7837step1Labels := by
      have ha : raw7837step1 = (fun i j => raw7837step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7837step1 raw7837step0; decide +kernel
      have hl : raw7837step1Labels = raw7837step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7837step0 raw7837step0Labels permutation151 permutation3
    mixedMoment B raw7837step1 raw7837step1Labels = mixedMoment B raw7837step2 raw7837step2Labels := by
      have ha : raw7837step2 = -raw7837step1 := by apply Matrix.ext; change ∀ i j, raw7837step2 i j = -(raw7837step1 i j); unfold raw7837step2 raw7837step1; decide +kernel
      have hl : raw7837step2Labels = raw7837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw7838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw7838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7838 raw7838Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw7838 raw7838Labels = mixedMoment B raw7838step0 raw7838step0Labels := by
      have hz : ∀ j, raw7838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7838step0 = (fun i j => raw7838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7838step0 raw7838; decide +kernel
      have hl : raw7838step0Labels = raw7838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7838 raw7838Labels permutation346 hz
    mixedMoment B raw7838step0 raw7838step0Labels = mixedMoment B raw7838step1 raw7838step1Labels := by
      have hz : ∀ j, raw7838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7838step1 = (fun i j => raw7838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7838step1 raw7838step0; decide +kernel
      have hl : raw7838step1Labels = raw7838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7838step0 raw7838step0Labels permutation56 hz
    mixedMoment B raw7838step1 raw7838step1Labels = mixedMoment B raw7838step2 raw7838step2Labels := by
      have ha : raw7838step2 = (fun i j => raw7838step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7838step2 raw7838step1; decide +kernel
      have hl : raw7838step2Labels = raw7838step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7838step1 raw7838step1Labels permutation31 permutation3
    mixedMoment B raw7838step2 raw7838step2Labels = mixedMoment B raw7838step3 raw7838step3Labels := by
      have ha : raw7838step3 = -raw7838step2 := by apply Matrix.ext; change ∀ i j, raw7838step3 i j = -(raw7838step2 i j); unfold raw7838step3 raw7838step2; decide +kernel
      have hl : raw7838step3Labels = raw7838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw7839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7839step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw7839step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7839step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw7839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7839step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw7839step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7839 raw7839Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw7839 raw7839Labels = mixedMoment B raw7839step0 raw7839step0Labels := by
      have hz : ∀ j, raw7839 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7839step0 = (fun i j => raw7839 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7839step0 raw7839; decide +kernel
      have hl : raw7839step0Labels = raw7839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7839 raw7839Labels permutation520 hz
    mixedMoment B raw7839step0 raw7839step0Labels = mixedMoment B raw7839step1 raw7839step1Labels := by
      have hz : ∀ j, raw7839step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7839step1 = (fun i j => raw7839step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7839step1 raw7839step0; decide +kernel
      have hl : raw7839step1Labels = raw7839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7839step0 raw7839step0Labels permutation80 hz
    mixedMoment B raw7839step1 raw7839step1Labels = mixedMoment B raw7839step2 raw7839step2Labels := by
      have hz : ∀ j, raw7839step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7839step2 = (fun i j => raw7839step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7839step2 raw7839step1; decide +kernel
      have hl : raw7839step2Labels = raw7839step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7839step1 raw7839step1Labels permutation14 hz
    mixedMoment B raw7839step2 raw7839step2Labels = mixedMoment B raw7839step3 raw7839step3Labels := by
      have ha : raw7839step3 = (fun i j => raw7839step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7839step3 raw7839step2; decide +kernel
      have hl : raw7839step3Labels = raw7839step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7839step2 raw7839step2Labels permutation7 permutation3
    mixedMoment B raw7839step3 raw7839step3Labels = mixedMoment B raw7839step4 raw7839step4Labels := by
      have ha : raw7839step4 = -raw7839step3 := by apply Matrix.ext; change ∀ i j, raw7839step4 i j = -(raw7839step3 i j); unfold raw7839step4 raw7839step3; decide +kernel
      have hl : raw7839step4Labels = raw7839step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw7840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7840 raw7840Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw7840 raw7840Labels = mixedMoment B raw7840step0 raw7840step0Labels := by
      have hz : ∀ j, raw7840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7840step0 = (fun i j => raw7840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7840step0 raw7840; decide +kernel
      have hl : raw7840step0Labels = raw7840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7840 raw7840Labels permutation346 hz
    mixedMoment B raw7840step0 raw7840step0Labels = mixedMoment B raw7840step1 raw7840step1Labels := by
      have hz : ∀ j, raw7840step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7840step1 = (fun i j => raw7840step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7840step1 raw7840step0; decide +kernel
      have hl : raw7840step1Labels = raw7840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7840step0 raw7840step0Labels permutation56 hz
    mixedMoment B raw7840step1 raw7840step1Labels = mixedMoment B raw7840step2 raw7840step2Labels := by
      have ha : raw7840step2 = (fun i j => raw7840step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7840step2 raw7840step1; decide +kernel
      have hl : raw7840step2Labels = raw7840step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7840step1 raw7840step1Labels permutation9 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw7841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7841 raw7841Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw7841 raw7841Labels = mixedMoment B raw7841step0 raw7841step0Labels := by
      have hz : ∀ j, raw7841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7841step0 = (fun i j => raw7841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7841step0 raw7841; decide +kernel
      have hl : raw7841step0Labels = raw7841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7841 raw7841Labels permutation346 hz
    mixedMoment B raw7841step0 raw7841step0Labels = mixedMoment B raw7841step1 raw7841step1Labels := by
      have ha : raw7841step1 = (fun i j => raw7841step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7841step1 raw7841step0; decide +kernel
      have hl : raw7841step1Labels = raw7841step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7841step0 raw7841step0Labels permutation38 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw7842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7842 raw7842Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw7842 raw7842Labels = mixedMoment B raw7842step0 raw7842step0Labels := by
      have ha : raw7842step0 = (fun i j => raw7842 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7842step0 raw7842; decide +kernel
      have hl : raw7842step0Labels = raw7842Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7842 raw7842Labels permutation182 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw7843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7843 raw7843Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw7843 raw7843Labels = mixedMoment B raw7843step0 raw7843step0Labels := by
      have hz : ∀ j, raw7843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7843step0 = (fun i j => raw7843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7843step0 raw7843; decide +kernel
      have hl : raw7843step0Labels = raw7843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7843 raw7843Labels permutation346 hz
    mixedMoment B raw7843step0 raw7843step0Labels = mixedMoment B raw7843step1 raw7843step1Labels := by
      have ha : raw7843step1 = (fun i j => raw7843step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7843step1 raw7843step0; decide +kernel
      have hl : raw7843step1Labels = raw7843step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7843step0 raw7843step0Labels permutation38 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw7844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7844step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7844 raw7844Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw7844 raw7844Labels = mixedMoment B raw7844step0 raw7844step0Labels := by
      have hz : ∀ j, raw7844 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7844step0 = (fun i j => raw7844 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7844step0 raw7844; decide +kernel
      have hl : raw7844step0Labels = raw7844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7844 raw7844Labels permutation520 hz
    mixedMoment B raw7844step0 raw7844step0Labels = mixedMoment B raw7844step1 raw7844step1Labels := by
      have hz : ∀ j, raw7844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7844step1 = (fun i j => raw7844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7844step1 raw7844step0; decide +kernel
      have hl : raw7844step1Labels = raw7844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7844step0 raw7844step0Labels permutation80 hz
    mixedMoment B raw7844step1 raw7844step1Labels = mixedMoment B raw7844step2 raw7844step2Labels := by
      have ha : raw7844step2 = (fun i j => raw7844step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7844step2 raw7844step1; decide +kernel
      have hl : raw7844step2Labels = raw7844step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7844step1 raw7844step1Labels permutation10 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw7845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7845 raw7845Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw7845 raw7845Labels = mixedMoment B raw7845step0 raw7845step0Labels := by
      have hz : ∀ j, raw7845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7845step0 = (fun i j => raw7845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7845step0 raw7845; decide +kernel
      have hl : raw7845step0Labels = raw7845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7845 raw7845Labels permutation346 hz
    mixedMoment B raw7845step0 raw7845step0Labels = mixedMoment B raw7845step1 raw7845step1Labels := by
      have ha : raw7845step1 = (fun i j => raw7845step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7845step1 raw7845step0; decide +kernel
      have hl : raw7845step1Labels = raw7845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7845step0 raw7845step0Labels permutation42 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw7846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7846 raw7846Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw7846 raw7846Labels = mixedMoment B raw7846step0 raw7846step0Labels := by
      have hz : ∀ j, raw7846 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7846step0 = (fun i j => raw7846 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7846step0 raw7846; decide +kernel
      have hl : raw7846step0Labels = raw7846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7846 raw7846Labels permutation265 hz
    mixedMoment B raw7846step0 raw7846step0Labels = mixedMoment B raw7846step1 raw7846step1Labels := by
      have ha : raw7846step1 = (fun i j => raw7846step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7846step1 raw7846step0; decide +kernel
      have hl : raw7846step1Labels = raw7846step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7846step0 raw7846step0Labels permutation38 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw7847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7847 raw7847Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw7847 raw7847Labels = mixedMoment B raw7847step0 raw7847step0Labels := by
      have ha : raw7847step0 = (fun i j => raw7847 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7847step0 raw7847; decide +kernel
      have hl : raw7847step0Labels = raw7847Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7847 raw7847Labels permutation158 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw7848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7848 raw7848Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw7848 raw7848Labels = mixedMoment B raw7848step0 raw7848step0Labels := by
      have hz : ∀ j, raw7848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7848step0 = (fun i j => raw7848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7848step0 raw7848; decide +kernel
      have hl : raw7848step0Labels = raw7848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7848 raw7848Labels permutation265 hz
    mixedMoment B raw7848step0 raw7848step0Labels = mixedMoment B raw7848step1 raw7848step1Labels := by
      have ha : raw7848step1 = (fun i j => raw7848step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7848step1 raw7848step0; decide +kernel
      have hl : raw7848step1Labels = raw7848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7848step0 raw7848step0Labels permutation38 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw7849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw7849step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7849 raw7849Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw7849 raw7849Labels = mixedMoment B raw7849step0 raw7849step0Labels := by
      have hz : ∀ j, raw7849 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7849step0 = (fun i j => raw7849 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7849step0 raw7849; decide +kernel
      have hl : raw7849step0Labels = raw7849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7849 raw7849Labels permutation520 hz
    mixedMoment B raw7849step0 raw7849step0Labels = mixedMoment B raw7849step1 raw7849step1Labels := by
      have hz : ∀ j, raw7849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7849step1 = (fun i j => raw7849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7849step1 raw7849step0; decide +kernel
      have hl : raw7849step1Labels = raw7849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7849step0 raw7849step0Labels permutation56 hz
    mixedMoment B raw7849step1 raw7849step1Labels = mixedMoment B raw7849step2 raw7849step2Labels := by
      have ha : raw7849step2 = (fun i j => raw7849step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7849step2 raw7849step1; decide +kernel
      have hl : raw7849step2Labels = raw7849step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7849step1 raw7849step1Labels permutation10 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw7850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7850 raw7850Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw7850 raw7850Labels = mixedMoment B raw7850step0 raw7850step0Labels := by
      have hz : ∀ j, raw7850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7850step0 = (fun i j => raw7850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7850step0 raw7850; decide +kernel
      have hl : raw7850step0Labels = raw7850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7850 raw7850Labels permutation265 hz
    mixedMoment B raw7850step0 raw7850step0Labels = mixedMoment B raw7850step1 raw7850step1Labels := by
      have ha : raw7850step1 = (fun i j => raw7850step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7850step1 raw7850step0; decide +kernel
      have hl : raw7850step1Labels = raw7850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7850step0 raw7850step0Labels permutation42 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw7851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7851step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7851 raw7851Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw7851 raw7851Labels = mixedMoment B raw7851step0 raw7851step0Labels := by
      have hz : ∀ j, raw7851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7851step0 = (fun i j => raw7851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7851step0 raw7851; decide +kernel
      have hl : raw7851step0Labels = raw7851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7851 raw7851Labels permutation346 hz
    mixedMoment B raw7851step0 raw7851step0Labels = mixedMoment B raw7851step1 raw7851step1Labels := by
      have hz : ∀ j, raw7851step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7851step1 = (fun i j => raw7851step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7851step1 raw7851step0; decide +kernel
      have hl : raw7851step1Labels = raw7851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7851step0 raw7851step0Labels permutation56 hz
    mixedMoment B raw7851step1 raw7851step1Labels = mixedMoment B raw7851step2 raw7851step2Labels := by
      have ha : raw7851step2 = (fun i j => raw7851step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7851step2 raw7851step1; decide +kernel
      have hl : raw7851step2Labels = raw7851step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7851step1 raw7851step1Labels permutation8 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw7852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7852 raw7852Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw7852 raw7852Labels = mixedMoment B raw7852step0 raw7852step0Labels := by
      have hz : ∀ j, raw7852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7852step0 = (fun i j => raw7852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7852step0 raw7852; decide +kernel
      have hl : raw7852step0Labels = raw7852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7852 raw7852Labels permutation346 hz
    mixedMoment B raw7852step0 raw7852step0Labels = mixedMoment B raw7852step1 raw7852step1Labels := by
      have ha : raw7852step1 = (fun i j => raw7852step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7852step1 raw7852step0; decide +kernel
      have hl : raw7852step1Labels = raw7852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7852step0 raw7852step0Labels permutation32 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw7853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7853 raw7853Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw7853 raw7853Labels = mixedMoment B raw7853step0 raw7853step0Labels := by
      have hz : ∀ j, raw7853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7853step0 = (fun i j => raw7853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7853step0 raw7853; decide +kernel
      have hl : raw7853step0Labels = raw7853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7853 raw7853Labels permutation265 hz
    mixedMoment B raw7853step0 raw7853step0Labels = mixedMoment B raw7853step1 raw7853step1Labels := by
      have ha : raw7853step1 = (fun i j => raw7853step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7853step1 raw7853step0; decide +kernel
      have hl : raw7853step1Labels = raw7853step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7853step0 raw7853step0Labels permutation32 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw7854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7854step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7854step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7854step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7854 raw7854Labels = mixedMoment B node3123 node3123Labels := by
  calc
    mixedMoment B raw7854 raw7854Labels = mixedMoment B raw7854step0 raw7854step0Labels := by
      have hz : ∀ j, raw7854 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7854step0 = (fun i j => raw7854 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7854step0 raw7854; decide +kernel
      have hl : raw7854step0Labels = raw7854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7854 raw7854Labels permutation520 hz
    mixedMoment B raw7854step0 raw7854step0Labels = mixedMoment B raw7854step1 raw7854step1Labels := by
      have hz : ∀ j, raw7854step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7854step1 = (fun i j => raw7854step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7854step1 raw7854step0; decide +kernel
      have hl : raw7854step1Labels = raw7854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7854step0 raw7854step0Labels permutation80 hz
    mixedMoment B raw7854step1 raw7854step1Labels = mixedMoment B raw7854step2 raw7854step2Labels := by
      have hz : ∀ j, raw7854step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7854step2 = (fun i j => raw7854step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7854step2 raw7854step1; decide +kernel
      have hl : raw7854step2Labels = raw7854step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7854step1 raw7854step1Labels permutation14 hz
    mixedMoment B raw7854step2 raw7854step2Labels = mixedMoment B raw7854step3 raw7854step3Labels := by
      have ha : raw7854step3 = (fun i j => raw7854step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7854step3 raw7854step2; decide +kernel
      have hl : raw7854step3Labels = raw7854step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7854step2 raw7854step2Labels permutation2 permutation3
    _ = mixedMoment B node3123 node3123Labels := by rfl

def raw7855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7855step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7855 raw7855Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw7855 raw7855Labels = mixedMoment B raw7855step0 raw7855step0Labels := by
      have hz : ∀ j, raw7855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7855step0 = (fun i j => raw7855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7855step0 raw7855; decide +kernel
      have hl : raw7855step0Labels = raw7855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7855 raw7855Labels permutation346 hz
    mixedMoment B raw7855step0 raw7855step0Labels = mixedMoment B raw7855step1 raw7855step1Labels := by
      have hz : ∀ j, raw7855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7855step1 = (fun i j => raw7855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7855step1 raw7855step0; decide +kernel
      have hl : raw7855step1Labels = raw7855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7855step0 raw7855step0Labels permutation56 hz
    mixedMoment B raw7855step1 raw7855step1Labels = mixedMoment B raw7855step2 raw7855step2Labels := by
      have ha : raw7855step2 = (fun i j => raw7855step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7855step2 raw7855step1; decide +kernel
      have hl : raw7855step2Labels = raw7855step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7855step1 raw7855step1Labels permutation9 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw7856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7856step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7856 raw7856Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw7856 raw7856Labels = mixedMoment B raw7856step0 raw7856step0Labels := by
      have hz : ∀ j, raw7856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7856step0 = (fun i j => raw7856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7856step0 raw7856; decide +kernel
      have hl : raw7856step0Labels = raw7856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7856 raw7856Labels permutation346 hz
    mixedMoment B raw7856step0 raw7856step0Labels = mixedMoment B raw7856step1 raw7856step1Labels := by
      have hz : ∀ j, raw7856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7856step1 = (fun i j => raw7856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7856step1 raw7856step0; decide +kernel
      have hl : raw7856step1Labels = raw7856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7856step0 raw7856step0Labels permutation56 hz
    mixedMoment B raw7856step1 raw7856step1Labels = mixedMoment B raw7856step2 raw7856step2Labels := by
      have ha : raw7856step2 = (fun i j => raw7856step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7856step2 raw7856step1; decide +kernel
      have hl : raw7856step2Labels = raw7856step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7856step1 raw7856step1Labels permutation9 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw7857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7857 raw7857Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw7857 raw7857Labels = mixedMoment B raw7857step0 raw7857step0Labels := by
      have hz : ∀ j, raw7857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7857step0 = (fun i j => raw7857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7857step0 raw7857; decide +kernel
      have hl : raw7857step0Labels = raw7857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7857 raw7857Labels permutation346 hz
    mixedMoment B raw7857step0 raw7857step0Labels = mixedMoment B raw7857step1 raw7857step1Labels := by
      have ha : raw7857step1 = (fun i j => raw7857step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7857step1 raw7857step0; decide +kernel
      have hl : raw7857step1Labels = raw7857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7857step0 raw7857step0Labels permutation33 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw7858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7858 raw7858Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw7858 raw7858Labels = mixedMoment B raw7858step0 raw7858step0Labels := by
      have hz : ∀ j, raw7858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7858step0 = (fun i j => raw7858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7858step0 raw7858; decide +kernel
      have hl : raw7858step0Labels = raw7858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7858 raw7858Labels permutation265 hz
    mixedMoment B raw7858step0 raw7858step0Labels = mixedMoment B raw7858step1 raw7858step1Labels := by
      have ha : raw7858step1 = (fun i j => raw7858step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7858step1 raw7858step0; decide +kernel
      have hl : raw7858step1Labels = raw7858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7858step0 raw7858step0Labels permutation33 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw7859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7859step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw7859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7859 raw7859Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw7859 raw7859Labels = mixedMoment B raw7859step0 raw7859step0Labels := by
      have hz : ∀ j, raw7859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7859step0 = (fun i j => raw7859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7859step0 raw7859; decide +kernel
      have hl : raw7859step0Labels = raw7859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7859 raw7859Labels permutation346 hz
    mixedMoment B raw7859step0 raw7859step0Labels = mixedMoment B raw7859step1 raw7859step1Labels := by
      have hz : ∀ j, raw7859step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7859step1 = (fun i j => raw7859step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7859step1 raw7859step0; decide +kernel
      have hl : raw7859step1Labels = raw7859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7859step0 raw7859step0Labels permutation56 hz
    mixedMoment B raw7859step1 raw7859step1Labels = mixedMoment B raw7859step2 raw7859step2Labels := by
      have ha : raw7859step2 = (fun i j => raw7859step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7859step2 raw7859step1; decide +kernel
      have hl : raw7859step2Labels = raw7859step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7859step1 raw7859step1Labels permutation9 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw7860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7860step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7860 raw7860Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw7860 raw7860Labels = mixedMoment B raw7860step0 raw7860step0Labels := by
      have hz : ∀ j, raw7860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7860step0 = (fun i j => raw7860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7860step0 raw7860; decide +kernel
      have hl : raw7860step0Labels = raw7860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7860 raw7860Labels permutation346 hz
    mixedMoment B raw7860step0 raw7860step0Labels = mixedMoment B raw7860step1 raw7860step1Labels := by
      have hz : ∀ j, raw7860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7860step1 = (fun i j => raw7860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7860step1 raw7860step0; decide +kernel
      have hl : raw7860step1Labels = raw7860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7860step0 raw7860step0Labels permutation56 hz
    mixedMoment B raw7860step1 raw7860step1Labels = mixedMoment B raw7860step2 raw7860step2Labels := by
      have ha : raw7860step2 = (fun i j => raw7860step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7860step2 raw7860step1; decide +kernel
      have hl : raw7860step2Labels = raw7860step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7860step1 raw7860step1Labels permutation9 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw7861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7861step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw7861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7861 raw7861Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw7861 raw7861Labels = mixedMoment B raw7861step0 raw7861step0Labels := by
      have hz : ∀ j, raw7861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7861step0 = (fun i j => raw7861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7861step0 raw7861; decide +kernel
      have hl : raw7861step0Labels = raw7861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7861 raw7861Labels permutation346 hz
    mixedMoment B raw7861step0 raw7861step0Labels = mixedMoment B raw7861step1 raw7861step1Labels := by
      have hz : ∀ j, raw7861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7861step1 = (fun i j => raw7861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7861step1 raw7861step0; decide +kernel
      have hl : raw7861step1Labels = raw7861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7861step0 raw7861step0Labels permutation56 hz
    mixedMoment B raw7861step1 raw7861step1Labels = mixedMoment B raw7861step2 raw7861step2Labels := by
      have ha : raw7861step2 = (fun i j => raw7861step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7861step2 raw7861step1; decide +kernel
      have hl : raw7861step2Labels = raw7861step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7861step1 raw7861step1Labels permutation8 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw7862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7862 raw7862Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw7862 raw7862Labels = mixedMoment B raw7862step0 raw7862step0Labels := by
      have hz : ∀ j, raw7862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7862step0 = (fun i j => raw7862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7862step0 raw7862; decide +kernel
      have hl : raw7862step0Labels = raw7862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7862 raw7862Labels permutation346 hz
    mixedMoment B raw7862step0 raw7862step0Labels = mixedMoment B raw7862step1 raw7862step1Labels := by
      have ha : raw7862step1 = (fun i j => raw7862step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7862step1 raw7862step0; decide +kernel
      have hl : raw7862step1Labels = raw7862step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7862step0 raw7862step0Labels permutation151 permutation3
    mixedMoment B raw7862step1 raw7862step1Labels = mixedMoment B raw7862step2 raw7862step2Labels := by
      have ha : raw7862step2 = -raw7862step1 := by apply Matrix.ext; change ∀ i j, raw7862step2 i j = -(raw7862step1 i j); unfold raw7862step2 raw7862step1; decide +kernel
      have hl : raw7862step2Labels = raw7862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw7863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw7863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7863 raw7863Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw7863 raw7863Labels = mixedMoment B raw7863step0 raw7863step0Labels := by
      have hz : ∀ j, raw7863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7863step0 = (fun i j => raw7863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7863step0 raw7863; decide +kernel
      have hl : raw7863step0Labels = raw7863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7863 raw7863Labels permutation265 hz
    mixedMoment B raw7863step0 raw7863step0Labels = mixedMoment B raw7863step1 raw7863step1Labels := by
      have ha : raw7863step1 = (fun i j => raw7863step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7863step1 raw7863step0; decide +kernel
      have hl : raw7863step1Labels = raw7863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7863step0 raw7863step0Labels permutation151 permutation3
    mixedMoment B raw7863step1 raw7863step1Labels = mixedMoment B raw7863step2 raw7863step2Labels := by
      have ha : raw7863step2 = -raw7863step1 := by apply Matrix.ext; change ∀ i j, raw7863step2 i j = -(raw7863step1 i j); unfold raw7863step2 raw7863step1; decide +kernel
      have hl : raw7863step2Labels = raw7863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw7864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7864step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7864step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7864 raw7864Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw7864 raw7864Labels = mixedMoment B raw7864step0 raw7864step0Labels := by
      have hz : ∀ j, raw7864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7864step0 = (fun i j => raw7864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7864step0 raw7864; decide +kernel
      have hl : raw7864step0Labels = raw7864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7864 raw7864Labels permutation346 hz
    mixedMoment B raw7864step0 raw7864step0Labels = mixedMoment B raw7864step1 raw7864step1Labels := by
      have hz : ∀ j, raw7864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7864step1 = (fun i j => raw7864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7864step1 raw7864step0; decide +kernel
      have hl : raw7864step1Labels = raw7864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7864step0 raw7864step0Labels permutation56 hz
    mixedMoment B raw7864step1 raw7864step1Labels = mixedMoment B raw7864step2 raw7864step2Labels := by
      have ha : raw7864step2 = (fun i j => raw7864step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7864step2 raw7864step1; decide +kernel
      have hl : raw7864step2Labels = raw7864step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7864step1 raw7864step1Labels permutation31 permutation3
    mixedMoment B raw7864step2 raw7864step2Labels = mixedMoment B raw7864step3 raw7864step3Labels := by
      have ha : raw7864step3 = -raw7864step2 := by apply Matrix.ext; change ∀ i j, raw7864step3 i j = -(raw7864step2 i j); unfold raw7864step3 raw7864step2; decide +kernel
      have hl : raw7864step3Labels = raw7864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw7865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7865step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw7865step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7865step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7865step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw7865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7865step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw7865step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7865 raw7865Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw7865 raw7865Labels = mixedMoment B raw7865step0 raw7865step0Labels := by
      have hz : ∀ j, raw7865 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7865step0 = (fun i j => raw7865 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7865step0 raw7865; decide +kernel
      have hl : raw7865step0Labels = raw7865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7865 raw7865Labels permutation520 hz
    mixedMoment B raw7865step0 raw7865step0Labels = mixedMoment B raw7865step1 raw7865step1Labels := by
      have hz : ∀ j, raw7865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7865step1 = (fun i j => raw7865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7865step1 raw7865step0; decide +kernel
      have hl : raw7865step1Labels = raw7865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7865step0 raw7865step0Labels permutation80 hz
    mixedMoment B raw7865step1 raw7865step1Labels = mixedMoment B raw7865step2 raw7865step2Labels := by
      have hz : ∀ j, raw7865step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7865step2 = (fun i j => raw7865step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7865step2 raw7865step1; decide +kernel
      have hl : raw7865step2Labels = raw7865step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7865step1 raw7865step1Labels permutation14 hz
    mixedMoment B raw7865step2 raw7865step2Labels = mixedMoment B raw7865step3 raw7865step3Labels := by
      have ha : raw7865step3 = (fun i j => raw7865step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7865step3 raw7865step2; decide +kernel
      have hl : raw7865step3Labels = raw7865step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7865step2 raw7865step2Labels permutation7 permutation3
    mixedMoment B raw7865step3 raw7865step3Labels = mixedMoment B raw7865step4 raw7865step4Labels := by
      have ha : raw7865step4 = -raw7865step3 := by apply Matrix.ext; change ∀ i j, raw7865step4 i j = -(raw7865step3 i j); unfold raw7865step4 raw7865step3; decide +kernel
      have hl : raw7865step4Labels = raw7865step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw7866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7866 raw7866Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw7866 raw7866Labels = mixedMoment B raw7866step0 raw7866step0Labels := by
      have hz : ∀ j, raw7866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7866step0 = (fun i j => raw7866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7866step0 raw7866; decide +kernel
      have hl : raw7866step0Labels = raw7866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7866 raw7866Labels permutation346 hz
    mixedMoment B raw7866step0 raw7866step0Labels = mixedMoment B raw7866step1 raw7866step1Labels := by
      have hz : ∀ j, raw7866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7866step1 = (fun i j => raw7866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7866step1 raw7866step0; decide +kernel
      have hl : raw7866step1Labels = raw7866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7866step0 raw7866step0Labels permutation56 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw7867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7867step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7867 raw7867Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw7867 raw7867Labels = mixedMoment B raw7867step0 raw7867step0Labels := by
      have hz : ∀ j, raw7867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7867step0 = (fun i j => raw7867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7867step0 raw7867; decide +kernel
      have hl : raw7867step0Labels = raw7867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7867 raw7867Labels permutation346 hz
    mixedMoment B raw7867step0 raw7867step0Labels = mixedMoment B raw7867step1 raw7867step1Labels := by
      have ha : raw7867step1 = (fun i j => raw7867step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7867step1 raw7867step0; decide +kernel
      have hl : raw7867step1Labels = raw7867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7867step0 raw7867step0Labels permutation40 permutation3
    mixedMoment B raw7867step1 raw7867step1Labels = mixedMoment B raw7867step2 raw7867step2Labels := by
      have ha : raw7867step2 = raw7867step1 := by apply Matrix.ext; unfold raw7867step2 raw7867step1; decide +kernel
      have hl : raw7867step1Labels = labelEmbedding6 ∘ raw7867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7867step1 raw7867step1Labels raw7867step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw7868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7868 raw7868Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw7868 raw7868Labels = mixedMoment B raw7868step0 raw7868step0Labels := by
      have ha : raw7868step0 = (fun i j => raw7868 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7868step0 raw7868; decide +kernel
      have hl : raw7868step0Labels = raw7868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7868 raw7868Labels permutation184 permutation3
    mixedMoment B raw7868step0 raw7868step0Labels = mixedMoment B raw7868step1 raw7868step1Labels := by
      have ha : raw7868step1 = raw7868step0 := by apply Matrix.ext; unfold raw7868step1 raw7868step0; decide +kernel
      have hl : raw7868step0Labels = labelEmbedding6 ∘ raw7868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7868step0 raw7868step0Labels raw7868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw7869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7869step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7869 raw7869Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw7869 raw7869Labels = mixedMoment B raw7869step0 raw7869step0Labels := by
      have hz : ∀ j, raw7869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7869step0 = (fun i j => raw7869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7869step0 raw7869; decide +kernel
      have hl : raw7869step0Labels = raw7869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7869 raw7869Labels permutation346 hz
    mixedMoment B raw7869step0 raw7869step0Labels = mixedMoment B raw7869step1 raw7869step1Labels := by
      have ha : raw7869step1 = (fun i j => raw7869step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7869step1 raw7869step0; decide +kernel
      have hl : raw7869step1Labels = raw7869step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7869step0 raw7869step0Labels permutation40 permutation3
    mixedMoment B raw7869step1 raw7869step1Labels = mixedMoment B raw7869step2 raw7869step2Labels := by
      have ha : raw7869step2 = raw7869step1 := by apply Matrix.ext; unfold raw7869step2 raw7869step1; decide +kernel
      have hl : raw7869step1Labels = labelEmbedding6 ∘ raw7869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7869step1 raw7869step1Labels raw7869step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw7870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7870step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7870 raw7870Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7870 raw7870Labels = mixedMoment B raw7870step0 raw7870step0Labels := by
      have hz : ∀ j, raw7870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7870step0 = (fun i j => raw7870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7870step0 raw7870; decide +kernel
      have hl : raw7870step0Labels = raw7870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7870 raw7870Labels permutation346 hz
    mixedMoment B raw7870step0 raw7870step0Labels = mixedMoment B raw7870step1 raw7870step1Labels := by
      have ha : raw7870step1 = (fun i j => raw7870step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7870step1 raw7870step0; decide +kernel
      have hl : raw7870step1Labels = raw7870step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7870step0 raw7870step0Labels permutation46 permutation3
    mixedMoment B raw7870step1 raw7870step1Labels = mixedMoment B raw7870step2 raw7870step2Labels := by
      have ha : raw7870step2 = raw7870step1 := by apply Matrix.ext; unfold raw7870step2 raw7870step1; decide +kernel
      have hl : raw7870step1Labels = labelEmbedding6 ∘ raw7870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7870step1 raw7870step1Labels raw7870step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7871step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7871 raw7871Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw7871 raw7871Labels = mixedMoment B raw7871step0 raw7871step0Labels := by
      have hz : ∀ j, raw7871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7871step0 = (fun i j => raw7871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7871step0 raw7871; decide +kernel
      have hl : raw7871step0Labels = raw7871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7871 raw7871Labels permutation265 hz
    mixedMoment B raw7871step0 raw7871step0Labels = mixedMoment B raw7871step1 raw7871step1Labels := by
      have ha : raw7871step1 = (fun i j => raw7871step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7871step1 raw7871step0; decide +kernel
      have hl : raw7871step1Labels = raw7871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7871step0 raw7871step0Labels permutation40 permutation3
    mixedMoment B raw7871step1 raw7871step1Labels = mixedMoment B raw7871step2 raw7871step2Labels := by
      have ha : raw7871step2 = raw7871step1 := by apply Matrix.ext; unfold raw7871step2 raw7871step1; decide +kernel
      have hl : raw7871step1Labels = labelEmbedding6 ∘ raw7871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7871step1 raw7871step1Labels raw7871step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw7872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7872step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7872 raw7872Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw7872 raw7872Labels = mixedMoment B raw7872step0 raw7872step0Labels := by
      have ha : raw7872step0 = (fun i j => raw7872 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7872step0 raw7872; decide +kernel
      have hl : raw7872step0Labels = raw7872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7872 raw7872Labels permutation160 permutation3
    mixedMoment B raw7872step0 raw7872step0Labels = mixedMoment B raw7872step1 raw7872step1Labels := by
      have ha : raw7872step1 = raw7872step0 := by apply Matrix.ext; unfold raw7872step1 raw7872step0; decide +kernel
      have hl : raw7872step0Labels = labelEmbedding6 ∘ raw7872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7872step0 raw7872step0Labels raw7872step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw7873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7873step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7873 raw7873Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw7873 raw7873Labels = mixedMoment B raw7873step0 raw7873step0Labels := by
      have hz : ∀ j, raw7873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7873step0 = (fun i j => raw7873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7873step0 raw7873; decide +kernel
      have hl : raw7873step0Labels = raw7873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7873 raw7873Labels permutation265 hz
    mixedMoment B raw7873step0 raw7873step0Labels = mixedMoment B raw7873step1 raw7873step1Labels := by
      have ha : raw7873step1 = (fun i j => raw7873step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7873step1 raw7873step0; decide +kernel
      have hl : raw7873step1Labels = raw7873step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7873step0 raw7873step0Labels permutation40 permutation3
    mixedMoment B raw7873step1 raw7873step1Labels = mixedMoment B raw7873step2 raw7873step2Labels := by
      have ha : raw7873step2 = raw7873step1 := by apply Matrix.ext; unfold raw7873step2 raw7873step1; decide +kernel
      have hl : raw7873step1Labels = labelEmbedding6 ∘ raw7873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7873step1 raw7873step1Labels raw7873step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw7874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7874step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7874 raw7874Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7874 raw7874Labels = mixedMoment B raw7874step0 raw7874step0Labels := by
      have hz : ∀ j, raw7874 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7874step0 = (fun i j => raw7874 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7874step0 raw7874; decide +kernel
      have hl : raw7874step0Labels = raw7874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7874 raw7874Labels permutation265 hz
    mixedMoment B raw7874step0 raw7874step0Labels = mixedMoment B raw7874step1 raw7874step1Labels := by
      have ha : raw7874step1 = (fun i j => raw7874step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7874step1 raw7874step0; decide +kernel
      have hl : raw7874step1Labels = raw7874step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7874step0 raw7874step0Labels permutation46 permutation3
    mixedMoment B raw7874step1 raw7874step1Labels = mixedMoment B raw7874step2 raw7874step2Labels := by
      have ha : raw7874step2 = raw7874step1 := by apply Matrix.ext; unfold raw7874step2 raw7874step1; decide +kernel
      have hl : raw7874step1Labels = labelEmbedding6 ∘ raw7874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7874step1 raw7874step1Labels raw7874step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7875step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7875step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7875 raw7875Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw7875 raw7875Labels = mixedMoment B raw7875step0 raw7875step0Labels := by
      have hz : ∀ j, raw7875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7875step0 = (fun i j => raw7875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7875step0 raw7875; decide +kernel
      have hl : raw7875step0Labels = raw7875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7875 raw7875Labels permutation346 hz
    mixedMoment B raw7875step0 raw7875step0Labels = mixedMoment B raw7875step1 raw7875step1Labels := by
      have hz : ∀ j, raw7875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7875step1 = (fun i j => raw7875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7875step1 raw7875step0; decide +kernel
      have hl : raw7875step1Labels = raw7875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7875step0 raw7875step0Labels permutation56 hz
    mixedMoment B raw7875step1 raw7875step1Labels = mixedMoment B raw7875step2 raw7875step2Labels := by
      have ha : raw7875step2 = (fun i j => raw7875step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7875step2 raw7875step1; decide +kernel
      have hl : raw7875step2Labels = raw7875step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7875step1 raw7875step1Labels permutation10 permutation3
    mixedMoment B raw7875step2 raw7875step2Labels = mixedMoment B raw7875step3 raw7875step3Labels := by
      have ha : raw7875step3 = raw7875step2 := by apply Matrix.ext; unfold raw7875step3 raw7875step2; decide +kernel
      have hl : raw7875step2Labels = labelEmbedding6 ∘ raw7875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7875step2 raw7875step2Labels raw7875step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw7876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7876step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7876 raw7876Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw7876 raw7876Labels = mixedMoment B raw7876step0 raw7876step0Labels := by
      have hz : ∀ j, raw7876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7876step0 = (fun i j => raw7876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7876step0 raw7876; decide +kernel
      have hl : raw7876step0Labels = raw7876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7876 raw7876Labels permutation346 hz
    mixedMoment B raw7876step0 raw7876step0Labels = mixedMoment B raw7876step1 raw7876step1Labels := by
      have ha : raw7876step1 = (fun i j => raw7876step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7876step1 raw7876step0; decide +kernel
      have hl : raw7876step1Labels = raw7876step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7876step0 raw7876step0Labels permutation34 permutation3
    mixedMoment B raw7876step1 raw7876step1Labels = mixedMoment B raw7876step2 raw7876step2Labels := by
      have ha : raw7876step2 = raw7876step1 := by apply Matrix.ext; unfold raw7876step2 raw7876step1; decide +kernel
      have hl : raw7876step1Labels = labelEmbedding6 ∘ raw7876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7876step1 raw7876step1Labels raw7876step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw7877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7877 raw7877Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw7877 raw7877Labels = mixedMoment B raw7877step0 raw7877step0Labels := by
      have hz : ∀ j, raw7877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7877step0 = (fun i j => raw7877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7877step0 raw7877; decide +kernel
      have hl : raw7877step0Labels = raw7877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7877 raw7877Labels permutation265 hz
    mixedMoment B raw7877step0 raw7877step0Labels = mixedMoment B raw7877step1 raw7877step1Labels := by
      have ha : raw7877step1 = (fun i j => raw7877step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7877step1 raw7877step0; decide +kernel
      have hl : raw7877step1Labels = raw7877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7877step0 raw7877step0Labels permutation34 permutation3
    mixedMoment B raw7877step1 raw7877step1Labels = mixedMoment B raw7877step2 raw7877step2Labels := by
      have ha : raw7877step2 = raw7877step1 := by apply Matrix.ext; unfold raw7877step2 raw7877step1; decide +kernel
      have hl : raw7877step1Labels = labelEmbedding6 ∘ raw7877step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7877step1 raw7877step1Labels raw7877step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw7878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7878step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7878 raw7878Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw7878 raw7878Labels = mixedMoment B raw7878step0 raw7878step0Labels := by
      have hz : ∀ j, raw7878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7878step0 = (fun i j => raw7878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7878step0 raw7878; decide +kernel
      have hl : raw7878step0Labels = raw7878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7878 raw7878Labels permutation346 hz
    mixedMoment B raw7878step0 raw7878step0Labels = mixedMoment B raw7878step1 raw7878step1Labels := by
      have hz : ∀ j, raw7878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7878step1 = (fun i j => raw7878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7878step1 raw7878step0; decide +kernel
      have hl : raw7878step1Labels = raw7878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7878step0 raw7878step0Labels permutation56 hz
    mixedMoment B raw7878step1 raw7878step1Labels = mixedMoment B raw7878step2 raw7878step2Labels := by
      have ha : raw7878step2 = (fun i j => raw7878step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7878step2 raw7878step1; decide +kernel
      have hl : raw7878step2Labels = raw7878step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7878step1 raw7878step1Labels permutation10 permutation3
    mixedMoment B raw7878step2 raw7878step2Labels = mixedMoment B raw7878step3 raw7878step3Labels := by
      have ha : raw7878step3 = raw7878step2 := by apply Matrix.ext; unfold raw7878step3 raw7878step2; decide +kernel
      have hl : raw7878step2Labels = labelEmbedding6 ∘ raw7878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7878step2 raw7878step2Labels raw7878step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw7879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7879 raw7879Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw7879 raw7879Labels = mixedMoment B raw7879step0 raw7879step0Labels := by
      have hz : ∀ j, raw7879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7879step0 = (fun i j => raw7879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7879step0 raw7879; decide +kernel
      have hl : raw7879step0Labels = raw7879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7879 raw7879Labels permutation346 hz
    mixedMoment B raw7879step0 raw7879step0Labels = mixedMoment B raw7879step1 raw7879step1Labels := by
      have hz : ∀ j, raw7879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7879step1 = (fun i j => raw7879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7879step1 raw7879step0; decide +kernel
      have hl : raw7879step1Labels = raw7879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7879step0 raw7879step0Labels permutation56 hz
    mixedMoment B raw7879step1 raw7879step1Labels = mixedMoment B raw7879step2 raw7879step2Labels := by
      have ha : raw7879step2 = (fun i j => raw7879step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7879step2 raw7879step1; decide +kernel
      have hl : raw7879step2Labels = raw7879step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7879step1 raw7879step1Labels permutation8 permutation3
    mixedMoment B raw7879step2 raw7879step2Labels = mixedMoment B raw7879step3 raw7879step3Labels := by
      have ha : raw7879step3 = raw7879step2 := by apply Matrix.ext; unfold raw7879step3 raw7879step2; decide +kernel
      have hl : raw7879step2Labels = labelEmbedding6 ∘ raw7879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7879step2 raw7879step2Labels raw7879step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw7880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7880 raw7880Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw7880 raw7880Labels = mixedMoment B raw7880step0 raw7880step0Labels := by
      have hz : ∀ j, raw7880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7880step0 = (fun i j => raw7880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7880step0 raw7880; decide +kernel
      have hl : raw7880step0Labels = raw7880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7880 raw7880Labels permutation346 hz
    mixedMoment B raw7880step0 raw7880step0Labels = mixedMoment B raw7880step1 raw7880step1Labels := by
      have ha : raw7880step1 = (fun i j => raw7880step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7880step1 raw7880step0; decide +kernel
      have hl : raw7880step1Labels = raw7880step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7880step0 raw7880step0Labels permutation32 permutation3
    mixedMoment B raw7880step1 raw7880step1Labels = mixedMoment B raw7880step2 raw7880step2Labels := by
      have ha : raw7880step2 = raw7880step1 := by apply Matrix.ext; unfold raw7880step2 raw7880step1; decide +kernel
      have hl : raw7880step1Labels = labelEmbedding6 ∘ raw7880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7880step1 raw7880step1Labels raw7880step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw7881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7881 raw7881Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw7881 raw7881Labels = mixedMoment B raw7881step0 raw7881step0Labels := by
      have hz : ∀ j, raw7881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7881step0 = (fun i j => raw7881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7881step0 raw7881; decide +kernel
      have hl : raw7881step0Labels = raw7881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7881 raw7881Labels permutation265 hz
    mixedMoment B raw7881step0 raw7881step0Labels = mixedMoment B raw7881step1 raw7881step1Labels := by
      have ha : raw7881step1 = (fun i j => raw7881step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7881step1 raw7881step0; decide +kernel
      have hl : raw7881step1Labels = raw7881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7881step0 raw7881step0Labels permutation32 permutation3
    mixedMoment B raw7881step1 raw7881step1Labels = mixedMoment B raw7881step2 raw7881step2Labels := by
      have ha : raw7881step2 = raw7881step1 := by apply Matrix.ext; unfold raw7881step2 raw7881step1; decide +kernel
      have hl : raw7881step1Labels = labelEmbedding6 ∘ raw7881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7881step1 raw7881step1Labels raw7881step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw7882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7882step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7882step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7882 raw7882Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw7882 raw7882Labels = mixedMoment B raw7882step0 raw7882step0Labels := by
      have hz : ∀ j, raw7882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7882step0 = (fun i j => raw7882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7882step0 raw7882; decide +kernel
      have hl : raw7882step0Labels = raw7882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7882 raw7882Labels permutation346 hz
    mixedMoment B raw7882step0 raw7882step0Labels = mixedMoment B raw7882step1 raw7882step1Labels := by
      have hz : ∀ j, raw7882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7882step1 = (fun i j => raw7882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7882step1 raw7882step0; decide +kernel
      have hl : raw7882step1Labels = raw7882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7882step0 raw7882step0Labels permutation56 hz
    mixedMoment B raw7882step1 raw7882step1Labels = mixedMoment B raw7882step2 raw7882step2Labels := by
      have ha : raw7882step2 = (fun i j => raw7882step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7882step2 raw7882step1; decide +kernel
      have hl : raw7882step2Labels = raw7882step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7882step1 raw7882step1Labels permutation8 permutation3
    mixedMoment B raw7882step2 raw7882step2Labels = mixedMoment B raw7882step3 raw7882step3Labels := by
      have ha : raw7882step3 = raw7882step2 := by apply Matrix.ext; unfold raw7882step3 raw7882step2; decide +kernel
      have hl : raw7882step2Labels = labelEmbedding6 ∘ raw7882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7882step2 raw7882step2Labels raw7882step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw7883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7883 raw7883Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw7883 raw7883Labels = mixedMoment B raw7883step0 raw7883step0Labels := by
      have hz : ∀ j, raw7883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7883step0 = (fun i j => raw7883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7883step0 raw7883; decide +kernel
      have hl : raw7883step0Labels = raw7883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7883 raw7883Labels permutation346 hz
    mixedMoment B raw7883step0 raw7883step0Labels = mixedMoment B raw7883step1 raw7883step1Labels := by
      have hz : ∀ j, raw7883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7883step1 = (fun i j => raw7883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7883step1 raw7883step0; decide +kernel
      have hl : raw7883step1Labels = raw7883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7883step0 raw7883step0Labels permutation56 hz
    mixedMoment B raw7883step1 raw7883step1Labels = mixedMoment B raw7883step2 raw7883step2Labels := by
      have ha : raw7883step2 = (fun i j => raw7883step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7883step2 raw7883step1; decide +kernel
      have hl : raw7883step2Labels = raw7883step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7883step1 raw7883step1Labels permutation8 permutation3
    mixedMoment B raw7883step2 raw7883step2Labels = mixedMoment B raw7883step3 raw7883step3Labels := by
      have ha : raw7883step3 = raw7883step2 := by apply Matrix.ext; unfold raw7883step3 raw7883step2; decide +kernel
      have hl : raw7883step2Labels = labelEmbedding6 ∘ raw7883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7883step2 raw7883step2Labels raw7883step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw7884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7884 raw7884Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw7884 raw7884Labels = mixedMoment B raw7884step0 raw7884step0Labels := by
      have hz : ∀ j, raw7884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7884step0 = (fun i j => raw7884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7884step0 raw7884; decide +kernel
      have hl : raw7884step0Labels = raw7884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7884 raw7884Labels permutation346 hz
    mixedMoment B raw7884step0 raw7884step0Labels = mixedMoment B raw7884step1 raw7884step1Labels := by
      have ha : raw7884step1 = (fun i j => raw7884step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7884step1 raw7884step0; decide +kernel
      have hl : raw7884step1Labels = raw7884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7884step0 raw7884step0Labels permutation32 permutation3
    mixedMoment B raw7884step1 raw7884step1Labels = mixedMoment B raw7884step2 raw7884step2Labels := by
      have ha : raw7884step2 = raw7884step1 := by apply Matrix.ext; unfold raw7884step2 raw7884step1; decide +kernel
      have hl : raw7884step1Labels = labelEmbedding6 ∘ raw7884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7884step1 raw7884step1Labels raw7884step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw7885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7885 raw7885Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw7885 raw7885Labels = mixedMoment B raw7885step0 raw7885step0Labels := by
      have hz : ∀ j, raw7885 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7885step0 = (fun i j => raw7885 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7885step0 raw7885; decide +kernel
      have hl : raw7885step0Labels = raw7885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7885 raw7885Labels permutation265 hz
    mixedMoment B raw7885step0 raw7885step0Labels = mixedMoment B raw7885step1 raw7885step1Labels := by
      have ha : raw7885step1 = (fun i j => raw7885step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7885step1 raw7885step0; decide +kernel
      have hl : raw7885step1Labels = raw7885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7885step0 raw7885step0Labels permutation32 permutation3
    mixedMoment B raw7885step1 raw7885step1Labels = mixedMoment B raw7885step2 raw7885step2Labels := by
      have ha : raw7885step2 = raw7885step1 := by apply Matrix.ext; unfold raw7885step2 raw7885step1; decide +kernel
      have hl : raw7885step1Labels = labelEmbedding6 ∘ raw7885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7885step1 raw7885step1Labels raw7885step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw7886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7886step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7886 raw7886Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw7886 raw7886Labels = mixedMoment B raw7886step0 raw7886step0Labels := by
      have hz : ∀ j, raw7886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7886step0 = (fun i j => raw7886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7886step0 raw7886; decide +kernel
      have hl : raw7886step0Labels = raw7886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7886 raw7886Labels permutation346 hz
    mixedMoment B raw7886step0 raw7886step0Labels = mixedMoment B raw7886step1 raw7886step1Labels := by
      have hz : ∀ j, raw7886step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7886step1 = (fun i j => raw7886step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7886step1 raw7886step0; decide +kernel
      have hl : raw7886step1Labels = raw7886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7886step0 raw7886step0Labels permutation56 hz
    mixedMoment B raw7886step1 raw7886step1Labels = mixedMoment B raw7886step2 raw7886step2Labels := by
      have ha : raw7886step2 = (fun i j => raw7886step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7886step2 raw7886step1; decide +kernel
      have hl : raw7886step2Labels = raw7886step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7886step1 raw7886step1Labels permutation8 permutation3
    mixedMoment B raw7886step2 raw7886step2Labels = mixedMoment B raw7886step3 raw7886step3Labels := by
      have ha : raw7886step3 = raw7886step2 := by apply Matrix.ext; unfold raw7886step3 raw7886step2; decide +kernel
      have hl : raw7886step2Labels = labelEmbedding6 ∘ raw7886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7886step2 raw7886step2Labels raw7886step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw7887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7887step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7887step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7887 raw7887Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw7887 raw7887Labels = mixedMoment B raw7887step0 raw7887step0Labels := by
      have hz : ∀ j, raw7887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7887step0 = (fun i j => raw7887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7887step0 raw7887; decide +kernel
      have hl : raw7887step0Labels = raw7887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7887 raw7887Labels permutation346 hz
    mixedMoment B raw7887step0 raw7887step0Labels = mixedMoment B raw7887step1 raw7887step1Labels := by
      have hz : ∀ j, raw7887step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7887step1 = (fun i j => raw7887step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7887step1 raw7887step0; decide +kernel
      have hl : raw7887step1Labels = raw7887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7887step0 raw7887step0Labels permutation56 hz
    mixedMoment B raw7887step1 raw7887step1Labels = mixedMoment B raw7887step2 raw7887step2Labels := by
      have ha : raw7887step2 = (fun i j => raw7887step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7887step2 raw7887step1; decide +kernel
      have hl : raw7887step2Labels = raw7887step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7887step1 raw7887step1Labels permutation10 permutation3
    mixedMoment B raw7887step2 raw7887step2Labels = mixedMoment B raw7887step3 raw7887step3Labels := by
      have ha : raw7887step3 = raw7887step2 := by apply Matrix.ext; unfold raw7887step3 raw7887step2; decide +kernel
      have hl : raw7887step2Labels = labelEmbedding6 ∘ raw7887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7887step2 raw7887step2Labels raw7887step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw7888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7888 raw7888Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw7888 raw7888Labels = mixedMoment B raw7888step0 raw7888step0Labels := by
      have hz : ∀ j, raw7888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7888step0 = (fun i j => raw7888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7888step0 raw7888; decide +kernel
      have hl : raw7888step0Labels = raw7888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7888 raw7888Labels permutation346 hz
    mixedMoment B raw7888step0 raw7888step0Labels = mixedMoment B raw7888step1 raw7888step1Labels := by
      have ha : raw7888step1 = (fun i j => raw7888step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7888step1 raw7888step0; decide +kernel
      have hl : raw7888step1Labels = raw7888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7888step0 raw7888step0Labels permutation32 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw7889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7889 raw7889Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw7889 raw7889Labels = mixedMoment B raw7889step0 raw7889step0Labels := by
      have hz : ∀ j, raw7889 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7889step0 = (fun i j => raw7889 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7889step0 raw7889; decide +kernel
      have hl : raw7889step0Labels = raw7889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7889 raw7889Labels permutation265 hz
    mixedMoment B raw7889step0 raw7889step0Labels = mixedMoment B raw7889step1 raw7889step1Labels := by
      have ha : raw7889step1 = (fun i j => raw7889step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7889step1 raw7889step0; decide +kernel
      have hl : raw7889step1Labels = raw7889step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7889step0 raw7889step0Labels permutation32 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw7890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7890step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw7890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7890 raw7890Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw7890 raw7890Labels = mixedMoment B raw7890step0 raw7890step0Labels := by
      have hz : ∀ j, raw7890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7890step0 = (fun i j => raw7890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7890step0 raw7890; decide +kernel
      have hl : raw7890step0Labels = raw7890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7890 raw7890Labels permutation346 hz
    mixedMoment B raw7890step0 raw7890step0Labels = mixedMoment B raw7890step1 raw7890step1Labels := by
      have hz : ∀ j, raw7890step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7890step1 = (fun i j => raw7890step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7890step1 raw7890step0; decide +kernel
      have hl : raw7890step1Labels = raw7890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7890step0 raw7890step0Labels permutation56 hz
    mixedMoment B raw7890step1 raw7890step1Labels = mixedMoment B raw7890step2 raw7890step2Labels := by
      have ha : raw7890step2 = (fun i j => raw7890step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7890step2 raw7890step1; decide +kernel
      have hl : raw7890step2Labels = raw7890step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7890step1 raw7890step1Labels permutation8 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw7891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7891 raw7891Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw7891 raw7891Labels = mixedMoment B raw7891step0 raw7891step0Labels := by
      have hz : ∀ j, raw7891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7891step0 = (fun i j => raw7891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7891step0 raw7891; decide +kernel
      have hl : raw7891step0Labels = raw7891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7891 raw7891Labels permutation346 hz
    mixedMoment B raw7891step0 raw7891step0Labels = mixedMoment B raw7891step1 raw7891step1Labels := by
      have hz : ∀ j, raw7891step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7891step1 = (fun i j => raw7891step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7891step1 raw7891step0; decide +kernel
      have hl : raw7891step1Labels = raw7891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7891step0 raw7891step0Labels permutation56 hz
    mixedMoment B raw7891step1 raw7891step1Labels = mixedMoment B raw7891step2 raw7891step2Labels := by
      have ha : raw7891step2 = (fun i j => raw7891step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7891step2 raw7891step1; decide +kernel
      have hl : raw7891step2Labels = raw7891step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7891step1 raw7891step1Labels permutation10 permutation3
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw7892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7892step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw7892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7892 raw7892Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw7892 raw7892Labels = mixedMoment B raw7892step0 raw7892step0Labels := by
      have hz : ∀ j, raw7892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7892step0 = (fun i j => raw7892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7892step0 raw7892; decide +kernel
      have hl : raw7892step0Labels = raw7892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7892 raw7892Labels permutation346 hz
    mixedMoment B raw7892step0 raw7892step0Labels = mixedMoment B raw7892step1 raw7892step1Labels := by
      have hz : ∀ j, raw7892step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7892step1 = (fun i j => raw7892step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7892step1 raw7892step0; decide +kernel
      have hl : raw7892step1Labels = raw7892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7892step0 raw7892step0Labels permutation56 hz
    mixedMoment B raw7892step1 raw7892step1Labels = mixedMoment B raw7892step2 raw7892step2Labels := by
      have ha : raw7892step2 = (fun i j => raw7892step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7892step2 raw7892step1; decide +kernel
      have hl : raw7892step2Labels = raw7892step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7892step1 raw7892step1Labels permutation8 permutation3
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw7893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7893 raw7893Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw7893 raw7893Labels = mixedMoment B raw7893step0 raw7893step0Labels := by
      have hz : ∀ j, raw7893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7893step0 = (fun i j => raw7893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7893step0 raw7893; decide +kernel
      have hl : raw7893step0Labels = raw7893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7893 raw7893Labels permutation346 hz
    mixedMoment B raw7893step0 raw7893step0Labels = mixedMoment B raw7893step1 raw7893step1Labels := by
      have ha : raw7893step1 = (fun i j => raw7893step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7893step1 raw7893step0; decide +kernel
      have hl : raw7893step1Labels = raw7893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7893step0 raw7893step0Labels permutation40 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw7894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7894 raw7894Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7894 raw7894Labels = mixedMoment B raw7894step0 raw7894step0Labels := by
      have ha : raw7894step0 = (fun i j => raw7894 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7894step0 raw7894; decide +kernel
      have hl : raw7894step0Labels = raw7894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7894 raw7894Labels permutation184 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw7895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7895 raw7895Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw7895 raw7895Labels = mixedMoment B raw7895step0 raw7895step0Labels := by
      have hz : ∀ j, raw7895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7895step0 = (fun i j => raw7895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7895step0 raw7895; decide +kernel
      have hl : raw7895step0Labels = raw7895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7895 raw7895Labels permutation346 hz
    mixedMoment B raw7895step0 raw7895step0Labels = mixedMoment B raw7895step1 raw7895step1Labels := by
      have ha : raw7895step1 = (fun i j => raw7895step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7895step1 raw7895step0; decide +kernel
      have hl : raw7895step1Labels = raw7895step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7895step0 raw7895step0Labels permutation40 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw7896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7896 raw7896Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7896 raw7896Labels = mixedMoment B raw7896step0 raw7896step0Labels := by
      have hz : ∀ j, raw7896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7896step0 = (fun i j => raw7896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7896step0 raw7896; decide +kernel
      have hl : raw7896step0Labels = raw7896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7896 raw7896Labels permutation346 hz
    mixedMoment B raw7896step0 raw7896step0Labels = mixedMoment B raw7896step1 raw7896step1Labels := by
      have ha : raw7896step1 = (fun i j => raw7896step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7896step1 raw7896step0; decide +kernel
      have hl : raw7896step1Labels = raw7896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7896step0 raw7896step0Labels permutation46 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7897 raw7897Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw7897 raw7897Labels = mixedMoment B raw7897step0 raw7897step0Labels := by
      have hz : ∀ j, raw7897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7897step0 = (fun i j => raw7897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7897step0 raw7897; decide +kernel
      have hl : raw7897step0Labels = raw7897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7897 raw7897Labels permutation346 hz
    mixedMoment B raw7897step0 raw7897step0Labels = mixedMoment B raw7897step1 raw7897step1Labels := by
      have ha : raw7897step1 = (fun i j => raw7897step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7897step1 raw7897step0; decide +kernel
      have hl : raw7897step1Labels = raw7897step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7897step0 raw7897step0Labels permutation41 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw7898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7898 raw7898Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw7898 raw7898Labels = mixedMoment B raw7898step0 raw7898step0Labels := by
      have hz : ∀ j, raw7898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7898step0 = (fun i j => raw7898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7898step0 raw7898; decide +kernel
      have hl : raw7898step0Labels = raw7898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7898 raw7898Labels permutation265 hz
    mixedMoment B raw7898step0 raw7898step0Labels = mixedMoment B raw7898step1 raw7898step1Labels := by
      have ha : raw7898step1 = (fun i j => raw7898step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7898step1 raw7898step0; decide +kernel
      have hl : raw7898step1Labels = raw7898step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7898step0 raw7898step0Labels permutation40 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw7899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7899 raw7899Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7899 raw7899Labels = mixedMoment B raw7899step0 raw7899step0Labels := by
      have ha : raw7899step0 = (fun i j => raw7899 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7899step0 raw7899; decide +kernel
      have hl : raw7899step0Labels = raw7899Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7899 raw7899Labels permutation160 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw7900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7900 raw7900Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw7900 raw7900Labels = mixedMoment B raw7900step0 raw7900step0Labels := by
      have hz : ∀ j, raw7900 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7900step0 = (fun i j => raw7900 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7900step0 raw7900; decide +kernel
      have hl : raw7900step0Labels = raw7900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7900 raw7900Labels permutation265 hz
    mixedMoment B raw7900step0 raw7900step0Labels = mixedMoment B raw7900step1 raw7900step1Labels := by
      have ha : raw7900step1 = (fun i j => raw7900step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7900step1 raw7900step0; decide +kernel
      have hl : raw7900step1Labels = raw7900step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7900step0 raw7900step0Labels permutation40 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw7901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7901step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7901 raw7901Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw7901 raw7901Labels = mixedMoment B raw7901step0 raw7901step0Labels := by
      have hz : ∀ j, raw7901 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7901step0 = (fun i j => raw7901 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7901step0 raw7901; decide +kernel
      have hl : raw7901step0Labels = raw7901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7901 raw7901Labels permutation265 hz
    mixedMoment B raw7901step0 raw7901step0Labels = mixedMoment B raw7901step1 raw7901step1Labels := by
      have ha : raw7901step1 = (fun i j => raw7901step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7901step1 raw7901step0; decide +kernel
      have hl : raw7901step1Labels = raw7901step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7901step0 raw7901step0Labels permutation46 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw7902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7902 raw7902Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw7902 raw7902Labels = mixedMoment B raw7902step0 raw7902step0Labels := by
      have hz : ∀ j, raw7902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7902step0 = (fun i j => raw7902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7902step0 raw7902; decide +kernel
      have hl : raw7902step0Labels = raw7902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7902 raw7902Labels permutation265 hz
    mixedMoment B raw7902step0 raw7902step0Labels = mixedMoment B raw7902step1 raw7902step1Labels := by
      have ha : raw7902step1 = (fun i j => raw7902step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7902step1 raw7902step0; decide +kernel
      have hl : raw7902step1Labels = raw7902step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7902step0 raw7902step0Labels permutation41 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw7903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7903step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7903 raw7903Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw7903 raw7903Labels = mixedMoment B raw7903step0 raw7903step0Labels := by
      have hz : ∀ j, raw7903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7903step0 = (fun i j => raw7903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7903step0 raw7903; decide +kernel
      have hl : raw7903step0Labels = raw7903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7903 raw7903Labels permutation346 hz
    mixedMoment B raw7903step0 raw7903step0Labels = mixedMoment B raw7903step1 raw7903step1Labels := by
      have hz : ∀ j, raw7903step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7903step1 = (fun i j => raw7903step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7903step1 raw7903step0; decide +kernel
      have hl : raw7903step1Labels = raw7903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7903step0 raw7903step0Labels permutation56 hz
    mixedMoment B raw7903step1 raw7903step1Labels = mixedMoment B raw7903step2 raw7903step2Labels := by
      have ha : raw7903step2 = (fun i j => raw7903step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7903step2 raw7903step1; decide +kernel
      have hl : raw7903step2Labels = raw7903step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7903step1 raw7903step1Labels permutation10 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw7904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7904 raw7904Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw7904 raw7904Labels = mixedMoment B raw7904step0 raw7904step0Labels := by
      have hz : ∀ j, raw7904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7904step0 = (fun i j => raw7904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7904step0 raw7904; decide +kernel
      have hl : raw7904step0Labels = raw7904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7904 raw7904Labels permutation346 hz
    mixedMoment B raw7904step0 raw7904step0Labels = mixedMoment B raw7904step1 raw7904step1Labels := by
      have ha : raw7904step1 = (fun i j => raw7904step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7904step1 raw7904step0; decide +kernel
      have hl : raw7904step1Labels = raw7904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7904step0 raw7904step0Labels permutation34 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw7905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw7905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw7905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7905 raw7905Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw7905 raw7905Labels = mixedMoment B raw7905step0 raw7905step0Labels := by
      have hz : ∀ j, raw7905 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7905step0 = (fun i j => raw7905 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7905step0 raw7905; decide +kernel
      have hl : raw7905step0Labels = raw7905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7905 raw7905Labels permutation265 hz
    mixedMoment B raw7905step0 raw7905step0Labels = mixedMoment B raw7905step1 raw7905step1Labels := by
      have ha : raw7905step1 = (fun i j => raw7905step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7905step1 raw7905step0; decide +kernel
      have hl : raw7905step1Labels = raw7905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7905step0 raw7905step0Labels permutation34 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw7906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw7906step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7906 raw7906Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw7906 raw7906Labels = mixedMoment B raw7906step0 raw7906step0Labels := by
      have hz : ∀ j, raw7906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7906step0 = (fun i j => raw7906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7906step0 raw7906; decide +kernel
      have hl : raw7906step0Labels = raw7906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7906 raw7906Labels permutation346 hz
    mixedMoment B raw7906step0 raw7906step0Labels = mixedMoment B raw7906step1 raw7906step1Labels := by
      have hz : ∀ j, raw7906step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7906step1 = (fun i j => raw7906step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7906step1 raw7906step0; decide +kernel
      have hl : raw7906step1Labels = raw7906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7906step0 raw7906step0Labels permutation56 hz
    mixedMoment B raw7906step1 raw7906step1Labels = mixedMoment B raw7906step2 raw7906step2Labels := by
      have ha : raw7906step2 = (fun i j => raw7906step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7906step2 raw7906step1; decide +kernel
      have hl : raw7906step2Labels = raw7906step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7906step1 raw7906step1Labels permutation10 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw7907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7907step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7907 raw7907Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw7907 raw7907Labels = mixedMoment B raw7907step0 raw7907step0Labels := by
      have hz : ∀ j, raw7907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7907step0 = (fun i j => raw7907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7907step0 raw7907; decide +kernel
      have hl : raw7907step0Labels = raw7907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7907 raw7907Labels permutation346 hz
    mixedMoment B raw7907step0 raw7907step0Labels = mixedMoment B raw7907step1 raw7907step1Labels := by
      have hz : ∀ j, raw7907step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7907step1 = (fun i j => raw7907step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7907step1 raw7907step0; decide +kernel
      have hl : raw7907step1Labels = raw7907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7907step0 raw7907step0Labels permutation56 hz
    mixedMoment B raw7907step1 raw7907step1Labels = mixedMoment B raw7907step2 raw7907step2Labels := by
      have ha : raw7907step2 = (fun i j => raw7907step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7907step2 raw7907step1; decide +kernel
      have hl : raw7907step2Labels = raw7907step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7907step1 raw7907step1Labels permutation11 permutation3
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw7908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7908 raw7908Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw7908 raw7908Labels = mixedMoment B raw7908step0 raw7908step0Labels := by
      have hz : ∀ j, raw7908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7908step0 = (fun i j => raw7908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7908step0 raw7908; decide +kernel
      have hl : raw7908step0Labels = raw7908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7908 raw7908Labels permutation346 hz
    mixedMoment B raw7908step0 raw7908step0Labels = mixedMoment B raw7908step1 raw7908step1Labels := by
      have hz : ∀ j, raw7908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7908step1 = (fun i j => raw7908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7908step1 raw7908step0; decide +kernel
      have hl : raw7908step1Labels = raw7908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7908step0 raw7908step0Labels permutation56 hz
    mixedMoment B raw7908step1 raw7908step1Labels = mixedMoment B raw7908step2 raw7908step2Labels := by
      have ha : raw7908step2 = (fun i j => raw7908step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7908step2 raw7908step1; decide +kernel
      have hl : raw7908step2Labels = raw7908step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7908step1 raw7908step1Labels permutation8 permutation3
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw7909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7909 raw7909Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw7909 raw7909Labels = mixedMoment B raw7909step0 raw7909step0Labels := by
      have hz : ∀ j, raw7909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7909step0 = (fun i j => raw7909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7909step0 raw7909; decide +kernel
      have hl : raw7909step0Labels = raw7909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7909 raw7909Labels permutation346 hz
    mixedMoment B raw7909step0 raw7909step0Labels = mixedMoment B raw7909step1 raw7909step1Labels := by
      have ha : raw7909step1 = (fun i j => raw7909step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7909step1 raw7909step0; decide +kernel
      have hl : raw7909step1Labels = raw7909step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7909step0 raw7909step0Labels permutation32 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw7910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw7910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7910 raw7910Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw7910 raw7910Labels = mixedMoment B raw7910step0 raw7910step0Labels := by
      have hz : ∀ j, raw7910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7910step0 = (fun i j => raw7910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7910step0 raw7910; decide +kernel
      have hl : raw7910step0Labels = raw7910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7910 raw7910Labels permutation265 hz
    mixedMoment B raw7910step0 raw7910step0Labels = mixedMoment B raw7910step1 raw7910step1Labels := by
      have ha : raw7910step1 = (fun i j => raw7910step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7910step1 raw7910step0; decide +kernel
      have hl : raw7910step1Labels = raw7910step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7910step0 raw7910step0Labels permutation32 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw7911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw7911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7911step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw7911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7911 raw7911Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw7911 raw7911Labels = mixedMoment B raw7911step0 raw7911step0Labels := by
      have hz : ∀ j, raw7911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7911step0 = (fun i j => raw7911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7911step0 raw7911; decide +kernel
      have hl : raw7911step0Labels = raw7911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7911 raw7911Labels permutation346 hz
    mixedMoment B raw7911step0 raw7911step0Labels = mixedMoment B raw7911step1 raw7911step1Labels := by
      have hz : ∀ j, raw7911step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7911step1 = (fun i j => raw7911step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7911step1 raw7911step0; decide +kernel
      have hl : raw7911step1Labels = raw7911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7911step0 raw7911step0Labels permutation56 hz
    mixedMoment B raw7911step1 raw7911step1Labels = mixedMoment B raw7911step2 raw7911step2Labels := by
      have ha : raw7911step2 = (fun i j => raw7911step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7911step2 raw7911step1; decide +kernel
      have hl : raw7911step2Labels = raw7911step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7911step1 raw7911step1Labels permutation8 permutation3
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw7912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw7912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7912 raw7912Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw7912 raw7912Labels = mixedMoment B raw7912step0 raw7912step0Labels := by
      have hz : ∀ j, raw7912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7912step0 = (fun i j => raw7912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7912step0 raw7912; decide +kernel
      have hl : raw7912step0Labels = raw7912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7912 raw7912Labels permutation346 hz
    mixedMoment B raw7912step0 raw7912step0Labels = mixedMoment B raw7912step1 raw7912step1Labels := by
      have hz : ∀ j, raw7912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7912step1 = (fun i j => raw7912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7912step1 raw7912step0; decide +kernel
      have hl : raw7912step1Labels = raw7912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7912step0 raw7912step0Labels permutation56 hz
    mixedMoment B raw7912step1 raw7912step1Labels = mixedMoment B raw7912step2 raw7912step2Labels := by
      have ha : raw7912step2 = (fun i j => raw7912step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7912step2 raw7912step1; decide +kernel
      have hl : raw7912step2Labels = raw7912step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7912step1 raw7912step1Labels permutation9 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw7913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7913 raw7913Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw7913 raw7913Labels = mixedMoment B raw7913step0 raw7913step0Labels := by
      have hz : ∀ j, raw7913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7913step0 = (fun i j => raw7913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7913step0 raw7913; decide +kernel
      have hl : raw7913step0Labels = raw7913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7913 raw7913Labels permutation346 hz
    mixedMoment B raw7913step0 raw7913step0Labels = mixedMoment B raw7913step1 raw7913step1Labels := by
      have hz : ∀ j, raw7913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7913step1 = (fun i j => raw7913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7913step1 raw7913step0; decide +kernel
      have hl : raw7913step1Labels = raw7913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7913step0 raw7913step0Labels permutation56 hz
    mixedMoment B raw7913step1 raw7913step1Labels = mixedMoment B raw7913step2 raw7913step2Labels := by
      have ha : raw7913step2 = (fun i j => raw7913step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7913step2 raw7913step1; decide +kernel
      have hl : raw7913step2Labels = raw7913step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7913step1 raw7913step1Labels permutation8 permutation3
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw7914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7914 raw7914Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw7914 raw7914Labels = mixedMoment B raw7914step0 raw7914step0Labels := by
      have hz : ∀ j, raw7914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7914step0 = (fun i j => raw7914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7914step0 raw7914; decide +kernel
      have hl : raw7914step0Labels = raw7914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7914 raw7914Labels permutation346 hz
    mixedMoment B raw7914step0 raw7914step0Labels = mixedMoment B raw7914step1 raw7914step1Labels := by
      have ha : raw7914step1 = (fun i j => raw7914step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7914step1 raw7914step0; decide +kernel
      have hl : raw7914step1Labels = raw7914step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7914step0 raw7914step0Labels permutation32 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw7915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7915 raw7915Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw7915 raw7915Labels = mixedMoment B raw7915step0 raw7915step0Labels := by
      have hz : ∀ j, raw7915 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7915step0 = (fun i j => raw7915 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7915step0 raw7915; decide +kernel
      have hl : raw7915step0Labels = raw7915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7915 raw7915Labels permutation265 hz
    mixedMoment B raw7915step0 raw7915step0Labels = mixedMoment B raw7915step1 raw7915step1Labels := by
      have ha : raw7915step1 = (fun i j => raw7915step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7915step1 raw7915step0; decide +kernel
      have hl : raw7915step1Labels = raw7915step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7915step0 raw7915step0Labels permutation32 permutation3
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw7916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7916step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw7916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7916 raw7916Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw7916 raw7916Labels = mixedMoment B raw7916step0 raw7916step0Labels := by
      have hz : ∀ j, raw7916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7916step0 = (fun i j => raw7916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7916step0 raw7916; decide +kernel
      have hl : raw7916step0Labels = raw7916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7916 raw7916Labels permutation346 hz
    mixedMoment B raw7916step0 raw7916step0Labels = mixedMoment B raw7916step1 raw7916step1Labels := by
      have hz : ∀ j, raw7916step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7916step1 = (fun i j => raw7916step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7916step1 raw7916step0; decide +kernel
      have hl : raw7916step1Labels = raw7916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7916step0 raw7916step0Labels permutation56 hz
    mixedMoment B raw7916step1 raw7916step1Labels = mixedMoment B raw7916step2 raw7916step2Labels := by
      have ha : raw7916step2 = (fun i j => raw7916step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7916step2 raw7916step1; decide +kernel
      have hl : raw7916step2Labels = raw7916step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7916step1 raw7916step1Labels permutation8 permutation3
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw7917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw7917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw7917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7917 raw7917Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw7917 raw7917Labels = mixedMoment B raw7917step0 raw7917step0Labels := by
      have hz : ∀ j, raw7917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7917step0 = (fun i j => raw7917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7917step0 raw7917; decide +kernel
      have hl : raw7917step0Labels = raw7917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7917 raw7917Labels permutation346 hz
    mixedMoment B raw7917step0 raw7917step0Labels = mixedMoment B raw7917step1 raw7917step1Labels := by
      have hz : ∀ j, raw7917step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7917step1 = (fun i j => raw7917step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7917step1 raw7917step0; decide +kernel
      have hl : raw7917step1Labels = raw7917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7917step0 raw7917step0Labels permutation56 hz
    mixedMoment B raw7917step1 raw7917step1Labels = mixedMoment B raw7917step2 raw7917step2Labels := by
      have ha : raw7917step2 = (fun i j => raw7917step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7917step2 raw7917step1; decide +kernel
      have hl : raw7917step2Labels = raw7917step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7917step1 raw7917step1Labels permutation10 permutation3
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw7918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7918step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7918 raw7918Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7918 raw7918Labels = mixedMoment B raw7918step0 raw7918step0Labels := by
      have hz : ∀ j, raw7918 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7918step0 = (fun i j => raw7918 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7918step0 raw7918; decide +kernel
      have hl : raw7918step0Labels = raw7918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7918 raw7918Labels permutation265 hz
    mixedMoment B raw7918step0 raw7918step0Labels = mixedMoment B raw7918step1 raw7918step1Labels := by
      have ha : raw7918step1 = (fun i j => raw7918step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7918step1 raw7918step0; decide +kernel
      have hl : raw7918step1Labels = raw7918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7918step0 raw7918step0Labels permutation38 permutation7
    mixedMoment B raw7918step1 raw7918step1Labels = mixedMoment B raw7918step2 raw7918step2Labels := by
      have ha : raw7918step2 = raw7918step1 := by apply Matrix.ext; unfold raw7918step2 raw7918step1; decide +kernel
      have hl : raw7918step1Labels = labelEmbedding10 ∘ raw7918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7918step1 raw7918step1Labels raw7918step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7919step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7919step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7919step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw7919step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7919 raw7919Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw7919 raw7919Labels = mixedMoment B raw7919step0 raw7919step0Labels := by
      have hz : ∀ j, raw7919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7919step0 = (fun i j => raw7919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7919step0 raw7919; decide +kernel
      have hl : raw7919step0Labels = raw7919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7919 raw7919Labels permutation434 hz
    mixedMoment B raw7919step0 raw7919step0Labels = mixedMoment B raw7919step1 raw7919step1Labels := by
      have hz : ∀ j, raw7919step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7919step1 = (fun i j => raw7919step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7919step1 raw7919step0; decide +kernel
      have hl : raw7919step1Labels = raw7919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7919step0 raw7919step0Labels permutation80 hz
    mixedMoment B raw7919step1 raw7919step1Labels = mixedMoment B raw7919step2 raw7919step2Labels := by
      have hz : ∀ j, raw7919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7919step2 = (fun i j => raw7919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7919step2 raw7919step1; decide +kernel
      have hl : raw7919step2Labels = raw7919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7919step1 raw7919step1Labels permutation14 hz
    mixedMoment B raw7919step2 raw7919step2Labels = mixedMoment B raw7919step3 raw7919step3Labels := by
      have ha : raw7919step3 = (fun i j => raw7919step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7919step3 raw7919step2; decide +kernel
      have hl : raw7919step3Labels = raw7919step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7919step2 raw7919step2Labels permutation2 permutation7
    mixedMoment B raw7919step3 raw7919step3Labels = mixedMoment B raw7919step4 raw7919step4Labels := by
      have ha : raw7919step4 = raw7919step3 := by apply Matrix.ext; unfold raw7919step4 raw7919step3; decide +kernel
      have hl : raw7919step3Labels = labelEmbedding10 ∘ raw7919step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7919step3 raw7919step3Labels raw7919step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw7920 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7920step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7920 raw7920Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw7920 raw7920Labels = mixedMoment B raw7920step0 raw7920step0Labels := by
      have hz : ∀ j, raw7920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7920step0 = (fun i j => raw7920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7920step0 raw7920; decide +kernel
      have hl : raw7920step0Labels = raw7920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7920 raw7920Labels permutation346 hz
    mixedMoment B raw7920step0 raw7920step0Labels = mixedMoment B raw7920step1 raw7920step1Labels := by
      have hz : ∀ j, raw7920step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7920step1 = (fun i j => raw7920step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7920step1 raw7920step0; decide +kernel
      have hl : raw7920step1Labels = raw7920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7920step0 raw7920step0Labels permutation56 hz
    mixedMoment B raw7920step1 raw7920step1Labels = mixedMoment B raw7920step2 raw7920step2Labels := by
      have ha : raw7920step2 = (fun i j => raw7920step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7920step2 raw7920step1; decide +kernel
      have hl : raw7920step2Labels = raw7920step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7920step1 raw7920step1Labels permutation8 permutation7
    mixedMoment B raw7920step2 raw7920step2Labels = mixedMoment B raw7920step3 raw7920step3Labels := by
      have ha : raw7920step3 = raw7920step2 := by apply Matrix.ext; unfold raw7920step3 raw7920step2; decide +kernel
      have hl : raw7920step2Labels = labelEmbedding10 ∘ raw7920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7920step2 raw7920step2Labels raw7920step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw7921 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw7921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7921 raw7921Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw7921 raw7921Labels = mixedMoment B raw7921step0 raw7921step0Labels := by
      have hz : ∀ j, raw7921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7921step0 = (fun i j => raw7921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7921step0 raw7921; decide +kernel
      have hl : raw7921step0Labels = raw7921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7921 raw7921Labels permutation346 hz
    mixedMoment B raw7921step0 raw7921step0Labels = mixedMoment B raw7921step1 raw7921step1Labels := by
      have hz : ∀ j, raw7921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7921step1 = (fun i j => raw7921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7921step1 raw7921step0; decide +kernel
      have hl : raw7921step1Labels = raw7921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7921step0 raw7921step0Labels permutation56 hz
    mixedMoment B raw7921step1 raw7921step1Labels = mixedMoment B raw7921step2 raw7921step2Labels := by
      have ha : raw7921step2 = (fun i j => raw7921step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7921step2 raw7921step1; decide +kernel
      have hl : raw7921step2Labels = raw7921step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7921step1 raw7921step1Labels permutation8 permutation7
    mixedMoment B raw7921step2 raw7921step2Labels = mixedMoment B raw7921step3 raw7921step3Labels := by
      have ha : raw7921step3 = raw7921step2 := by apply Matrix.ext; unfold raw7921step3 raw7921step2; decide +kernel
      have hl : raw7921step2Labels = labelEmbedding10 ∘ raw7921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7921step2 raw7921step2Labels raw7921step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw7922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7922step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7922 raw7922Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw7922 raw7922Labels = mixedMoment B raw7922step0 raw7922step0Labels := by
      have ha : raw7922step0 = (fun i j => raw7922 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7922step0 raw7922; decide +kernel
      have hl : raw7922step0Labels = raw7922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7922 raw7922Labels permutation176 permutation6
    mixedMoment B raw7922step0 raw7922step0Labels = mixedMoment B raw7922step1 raw7922step1Labels := by
      have ha : raw7922step1 = raw7922step0 := by apply Matrix.ext; unfold raw7922step1 raw7922step0; decide +kernel
      have hl : raw7922step0Labels = labelEmbedding9 ∘ raw7922step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7922step0 raw7922step0Labels raw7922step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw7923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7923step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7923 raw7923Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw7923 raw7923Labels = mixedMoment B raw7923step0 raw7923step0Labels := by
      have hz : ∀ j, raw7923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7923step0 = (fun i j => raw7923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7923step0 raw7923; decide +kernel
      have hl : raw7923step0Labels = raw7923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7923 raw7923Labels permutation434 hz
    mixedMoment B raw7923step0 raw7923step0Labels = mixedMoment B raw7923step1 raw7923step1Labels := by
      have hz : ∀ j, raw7923step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7923step1 = (fun i j => raw7923step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7923step1 raw7923step0; decide +kernel
      have hl : raw7923step1Labels = raw7923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7923step0 raw7923step0Labels permutation80 hz
    mixedMoment B raw7923step1 raw7923step1Labels = mixedMoment B raw7923step2 raw7923step2Labels := by
      have ha : raw7923step2 = (fun i j => raw7923step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7923step2 raw7923step1; decide +kernel
      have hl : raw7923step2Labels = raw7923step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7923step1 raw7923step1Labels permutation8 permutation6
    mixedMoment B raw7923step2 raw7923step2Labels = mixedMoment B raw7923step3 raw7923step3Labels := by
      have ha : raw7923step3 = raw7923step2 := by apply Matrix.ext; unfold raw7923step3 raw7923step2; decide +kernel
      have hl : raw7923step2Labels = labelEmbedding9 ∘ raw7923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7923step2 raw7923step2Labels raw7923step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw7924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7924step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7924 raw7924Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw7924 raw7924Labels = mixedMoment B raw7924step0 raw7924step0Labels := by
      have hz : ∀ j, raw7924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7924step0 = (fun i j => raw7924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7924step0 raw7924; decide +kernel
      have hl : raw7924step0Labels = raw7924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7924 raw7924Labels permutation346 hz
    mixedMoment B raw7924step0 raw7924step0Labels = mixedMoment B raw7924step1 raw7924step1Labels := by
      have ha : raw7924step1 = (fun i j => raw7924step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7924step1 raw7924step0; decide +kernel
      have hl : raw7924step1Labels = raw7924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7924step0 raw7924step0Labels permutation32 permutation6
    mixedMoment B raw7924step1 raw7924step1Labels = mixedMoment B raw7924step2 raw7924step2Labels := by
      have ha : raw7924step2 = raw7924step1 := by apply Matrix.ext; unfold raw7924step2 raw7924step1; decide +kernel
      have hl : raw7924step1Labels = labelEmbedding9 ∘ raw7924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7924step1 raw7924step1Labels raw7924step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw7925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7925step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7925 raw7925Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw7925 raw7925Labels = mixedMoment B raw7925step0 raw7925step0Labels := by
      have hz : ∀ j, raw7925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7925step0 = (fun i j => raw7925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7925step0 raw7925; decide +kernel
      have hl : raw7925step0Labels = raw7925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7925 raw7925Labels permutation346 hz
    mixedMoment B raw7925step0 raw7925step0Labels = mixedMoment B raw7925step1 raw7925step1Labels := by
      have hz : ∀ j, raw7925step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7925step1 = (fun i j => raw7925step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7925step1 raw7925step0; decide +kernel
      have hl : raw7925step1Labels = raw7925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7925step0 raw7925step0Labels permutation56 hz
    mixedMoment B raw7925step1 raw7925step1Labels = mixedMoment B raw7925step2 raw7925step2Labels := by
      have ha : raw7925step2 = (fun i j => raw7925step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7925step2 raw7925step1; decide +kernel
      have hl : raw7925step2Labels = raw7925step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7925step1 raw7925step1Labels permutation8 permutation6
    mixedMoment B raw7925step2 raw7925step2Labels = mixedMoment B raw7925step3 raw7925step3Labels := by
      have ha : raw7925step3 = raw7925step2 := by apply Matrix.ext; unfold raw7925step3 raw7925step2; decide +kernel
      have hl : raw7925step2Labels = labelEmbedding9 ∘ raw7925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7925step2 raw7925step2Labels raw7925step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw7926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw7926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7926step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7926 raw7926Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7926 raw7926Labels = mixedMoment B raw7926step0 raw7926step0Labels := by
      have hz : ∀ j, raw7926 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7926step0 = (fun i j => raw7926 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7926step0 raw7926; decide +kernel
      have hl : raw7926step0Labels = raw7926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7926 raw7926Labels permutation265 hz
    mixedMoment B raw7926step0 raw7926step0Labels = mixedMoment B raw7926step1 raw7926step1Labels := by
      have ha : raw7926step1 = (fun i j => raw7926step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7926step1 raw7926step0; decide +kernel
      have hl : raw7926step1Labels = raw7926step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7926step0 raw7926step0Labels permutation32 permutation6
    mixedMoment B raw7926step1 raw7926step1Labels = mixedMoment B raw7926step2 raw7926step2Labels := by
      have ha : raw7926step2 = raw7926step1 := by apply Matrix.ext; unfold raw7926step2 raw7926step1; decide +kernel
      have hl : raw7926step1Labels = labelEmbedding9 ∘ raw7926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7926step1 raw7926step1Labels raw7926step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7927 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7927step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7927step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7927step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7927step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7927step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7927 raw7927Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw7927 raw7927Labels = mixedMoment B raw7927step0 raw7927step0Labels := by
      have hz : ∀ j, raw7927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7927step0 = (fun i j => raw7927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7927step0 raw7927; decide +kernel
      have hl : raw7927step0Labels = raw7927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7927 raw7927Labels permutation346 hz
    mixedMoment B raw7927step0 raw7927step0Labels = mixedMoment B raw7927step1 raw7927step1Labels := by
      have hz : ∀ j, raw7927step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7927step1 = (fun i j => raw7927step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7927step1 raw7927step0; decide +kernel
      have hl : raw7927step1Labels = raw7927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7927step0 raw7927step0Labels permutation56 hz
    mixedMoment B raw7927step1 raw7927step1Labels = mixedMoment B raw7927step2 raw7927step2Labels := by
      have ha : raw7927step2 = (fun i j => raw7927step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7927step2 raw7927step1; decide +kernel
      have hl : raw7927step2Labels = raw7927step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7927step1 raw7927step1Labels permutation10 permutation4
    mixedMoment B raw7927step2 raw7927step2Labels = mixedMoment B raw7927step3 raw7927step3Labels := by
      have ha : raw7927step3 = -raw7927step2 := by apply Matrix.ext; change ∀ i j, raw7927step3 i j = -(raw7927step2 i j); unfold raw7927step3 raw7927step2; decide +kernel
      have hl : raw7927step3Labels = raw7927step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7927step3 raw7927step3Labels = mixedMoment B raw7927step4 raw7927step4Labels := by
      have ha : raw7927step4 = raw7927step3 := by apply Matrix.ext; unfold raw7927step4 raw7927step3; decide +kernel
      have hl : raw7927step3Labels = labelEmbedding7 ∘ raw7927step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7927step3 raw7927step3Labels raw7927step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw7928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7928step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7928 raw7928Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw7928 raw7928Labels = mixedMoment B raw7928step0 raw7928step0Labels := by
      have hz : ∀ j, raw7928 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7928step0 = (fun i j => raw7928 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7928step0 raw7928; decide +kernel
      have hl : raw7928step0Labels = raw7928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7928 raw7928Labels permutation265 hz
    mixedMoment B raw7928step0 raw7928step0Labels = mixedMoment B raw7928step1 raw7928step1Labels := by
      have ha : raw7928step1 = (fun i j => raw7928step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7928step1 raw7928step0; decide +kernel
      have hl : raw7928step1Labels = raw7928step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7928step0 raw7928step0Labels permutation32 permutation6
    mixedMoment B raw7928step1 raw7928step1Labels = mixedMoment B raw7928step2 raw7928step2Labels := by
      have ha : raw7928step2 = raw7928step1 := by apply Matrix.ext; unfold raw7928step2 raw7928step1; decide +kernel
      have hl : raw7928step1Labels = labelEmbedding9 ∘ raw7928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7928step1 raw7928step1Labels raw7928step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw7929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -2, 2]]
def raw7929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7929step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7929step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7929step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7929step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7929 raw7929Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw7929 raw7929Labels = mixedMoment B raw7929step0 raw7929step0Labels := by
      have hz : ∀ j, raw7929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7929step0 = (fun i j => raw7929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7929step0 raw7929; decide +kernel
      have hl : raw7929step0Labels = raw7929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7929 raw7929Labels permutation434 hz
    mixedMoment B raw7929step0 raw7929step0Labels = mixedMoment B raw7929step1 raw7929step1Labels := by
      have hz : ∀ j, raw7929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7929step1 = (fun i j => raw7929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7929step1 raw7929step0; decide +kernel
      have hl : raw7929step1Labels = raw7929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7929step0 raw7929step0Labels permutation80 hz
    mixedMoment B raw7929step1 raw7929step1Labels = mixedMoment B raw7929step2 raw7929step2Labels := by
      have hz : ∀ j, raw7929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7929step2 = (fun i j => raw7929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7929step2 raw7929step1; decide +kernel
      have hl : raw7929step2Labels = raw7929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7929step1 raw7929step1Labels permutation14 hz
    mixedMoment B raw7929step2 raw7929step2Labels = mixedMoment B raw7929step3 raw7929step3Labels := by
      have ha : raw7929step3 = (fun i j => raw7929step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7929step3 raw7929step2; decide +kernel
      have hl : raw7929step3Labels = raw7929step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7929step2 raw7929step2Labels permutation2 permutation6
    mixedMoment B raw7929step3 raw7929step3Labels = mixedMoment B raw7929step4 raw7929step4Labels := by
      have ha : raw7929step4 = raw7929step3 := by apply Matrix.ext; unfold raw7929step4 raw7929step3; decide +kernel
      have hl : raw7929step3Labels = labelEmbedding9 ∘ raw7929step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7929step3 raw7929step3Labels raw7929step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw7930 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw7930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7930step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7930step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw7930step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7930 raw7930Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw7930 raw7930Labels = mixedMoment B raw7930step0 raw7930step0Labels := by
      have hz : ∀ j, raw7930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7930step0 = (fun i j => raw7930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7930step0 raw7930; decide +kernel
      have hl : raw7930step0Labels = raw7930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7930 raw7930Labels permutation346 hz
    mixedMoment B raw7930step0 raw7930step0Labels = mixedMoment B raw7930step1 raw7930step1Labels := by
      have hz : ∀ j, raw7930step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7930step1 = (fun i j => raw7930step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7930step1 raw7930step0; decide +kernel
      have hl : raw7930step1Labels = raw7930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7930step0 raw7930step0Labels permutation56 hz
    mixedMoment B raw7930step1 raw7930step1Labels = mixedMoment B raw7930step2 raw7930step2Labels := by
      have ha : raw7930step2 = (fun i j => raw7930step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7930step2 raw7930step1; decide +kernel
      have hl : raw7930step2Labels = raw7930step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7930step1 raw7930step1Labels permutation8 permutation6
    mixedMoment B raw7930step2 raw7930step2Labels = mixedMoment B raw7930step3 raw7930step3Labels := by
      have ha : raw7930step3 = raw7930step2 := by apply Matrix.ext; unfold raw7930step3 raw7930step2; decide +kernel
      have hl : raw7930step2Labels = labelEmbedding9 ∘ raw7930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7930step2 raw7930step2Labels raw7930step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw7931 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7931 raw7931Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7931 raw7931Labels = mixedMoment B raw7931step0 raw7931step0Labels := by
      have hz : ∀ j, raw7931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7931step0 = (fun i j => raw7931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7931step0 raw7931; decide +kernel
      have hl : raw7931step0Labels = raw7931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7931 raw7931Labels permutation265 hz
    mixedMoment B raw7931step0 raw7931step0Labels = mixedMoment B raw7931step1 raw7931step1Labels := by
      have ha : raw7931step1 = (fun i j => raw7931step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7931step1 raw7931step0; decide +kernel
      have hl : raw7931step1Labels = raw7931step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7931step0 raw7931step0Labels permutation32 permutation6
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7932 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, -1, 2]]
def raw7932step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7932step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7932step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7932 raw7932Labels = mixedMoment B node3123 node3123Labels := by
  calc
    mixedMoment B raw7932 raw7932Labels = mixedMoment B raw7932step0 raw7932step0Labels := by
      have hz : ∀ j, raw7932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7932step0 = (fun i j => raw7932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7932step0 raw7932; decide +kernel
      have hl : raw7932step0Labels = raw7932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7932 raw7932Labels permutation434 hz
    mixedMoment B raw7932step0 raw7932step0Labels = mixedMoment B raw7932step1 raw7932step1Labels := by
      have hz : ∀ j, raw7932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7932step1 = (fun i j => raw7932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7932step1 raw7932step0; decide +kernel
      have hl : raw7932step1Labels = raw7932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7932step0 raw7932step0Labels permutation80 hz
    mixedMoment B raw7932step1 raw7932step1Labels = mixedMoment B raw7932step2 raw7932step2Labels := by
      have hz : ∀ j, raw7932step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7932step2 = (fun i j => raw7932step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7932step2 raw7932step1; decide +kernel
      have hl : raw7932step2Labels = raw7932step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7932step1 raw7932step1Labels permutation14 hz
    mixedMoment B raw7932step2 raw7932step2Labels = mixedMoment B raw7932step3 raw7932step3Labels := by
      have ha : raw7932step3 = (fun i j => raw7932step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7932step3 raw7932step2; decide +kernel
      have hl : raw7932step3Labels = raw7932step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7932step2 raw7932step2Labels permutation2 permutation6
    _ = mixedMoment B node3123 node3123Labels := by rfl

def raw7933 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw7933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7933 raw7933Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw7933 raw7933Labels = mixedMoment B raw7933step0 raw7933step0Labels := by
      have hz : ∀ j, raw7933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7933step0 = (fun i j => raw7933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7933step0 raw7933; decide +kernel
      have hl : raw7933step0Labels = raw7933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7933 raw7933Labels permutation346 hz
    mixedMoment B raw7933step0 raw7933step0Labels = mixedMoment B raw7933step1 raw7933step1Labels := by
      have hz : ∀ j, raw7933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7933step1 = (fun i j => raw7933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7933step1 raw7933step0; decide +kernel
      have hl : raw7933step1Labels = raw7933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7933step0 raw7933step0Labels permutation56 hz
    mixedMoment B raw7933step1 raw7933step1Labels = mixedMoment B raw7933step2 raw7933step2Labels := by
      have ha : raw7933step2 = (fun i j => raw7933step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7933step2 raw7933step1; decide +kernel
      have hl : raw7933step2Labels = raw7933step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7933step1 raw7933step1Labels permutation8 permutation6
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw7934 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7934 raw7934Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw7934 raw7934Labels = mixedMoment B raw7934step0 raw7934step0Labels := by
      have hz : ∀ j, raw7934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7934step0 = (fun i j => raw7934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7934step0 raw7934; decide +kernel
      have hl : raw7934step0Labels = raw7934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7934 raw7934Labels permutation346 hz
    mixedMoment B raw7934step0 raw7934step0Labels = mixedMoment B raw7934step1 raw7934step1Labels := by
      have hz : ∀ j, raw7934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7934step1 = (fun i j => raw7934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7934step1 raw7934step0; decide +kernel
      have hl : raw7934step1Labels = raw7934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7934step0 raw7934step0Labels permutation56 hz
    mixedMoment B raw7934step1 raw7934step1Labels = mixedMoment B raw7934step2 raw7934step2Labels := by
      have ha : raw7934step2 = (fun i j => raw7934step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7934step2 raw7934step1; decide +kernel
      have hl : raw7934step2Labels = raw7934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7934step1 raw7934step1Labels permutation8 permutation6
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw7935 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7935 raw7935Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw7935 raw7935Labels = mixedMoment B raw7935step0 raw7935step0Labels := by
      have ha : raw7935step0 = (fun i j => raw7935 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7935step0 raw7935; decide +kernel
      have hl : raw7935step0Labels = raw7935Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7935 raw7935Labels permutation176 permutation6
    _ = mixedMoment B node2709 node2709Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
