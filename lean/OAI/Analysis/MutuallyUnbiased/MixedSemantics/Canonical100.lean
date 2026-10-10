import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12800 raw12800Labels = mixedMoment B node1052 node1052Labels := by
  calc
    mixedMoment B raw12800 raw12800Labels = mixedMoment B raw12800step0 raw12800step0Labels := by
      have ha : raw12800step0 = (fun i j => raw12800 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12800step0 raw12800; decide +kernel
      have hl : raw12800step0Labels = raw12800Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12800 raw12800Labels permutation184 permutation3
    _ = mixedMoment B node1052 node1052Labels := by rfl

def raw12801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12801 raw12801Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw12801 raw12801Labels = mixedMoment B raw12801step0 raw12801step0Labels := by
      have ha : raw12801step0 = (fun i j => raw12801 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12801step0 raw12801; decide +kernel
      have hl : raw12801step0Labels = raw12801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12801 raw12801Labels permutation184 permutation3
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw12802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12802 raw12802Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw12802 raw12802Labels = mixedMoment B raw12802step0 raw12802step0Labels := by
      have ha : raw12802step0 = (fun i j => raw12802 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12802step0 raw12802; decide +kernel
      have hl : raw12802step0Labels = raw12802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12802 raw12802Labels permutation208 permutation3
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw12803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12803 raw12803Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw12803 raw12803Labels = mixedMoment B raw12803step0 raw12803step0Labels := by
      have ha : raw12803step0 = (fun i j => raw12803 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12803step0 raw12803; decide +kernel
      have hl : raw12803step0Labels = raw12803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12803 raw12803Labels permutation232 permutation3
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw12804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12804 raw12804Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12804 raw12804Labels = mixedMoment B raw12804step0 raw12804step0Labels := by
      have hz : ∀ j, raw12804 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12804step0 = (fun i j => raw12804 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12804step0 raw12804; decide +kernel
      have hl : raw12804step0Labels = raw12804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12804 raw12804Labels permutation590 hz
    mixedMoment B raw12804step0 raw12804step0Labels = mixedMoment B raw12804step1 raw12804step1Labels := by
      have ha : raw12804step1 = (fun i j => raw12804step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12804step1 raw12804step0; decide +kernel
      have hl : raw12804step1Labels = raw12804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12804step0 raw12804step0Labels permutation41 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12805 raw12805Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw12805 raw12805Labels = mixedMoment B raw12805step0 raw12805step0Labels := by
      have hz : ∀ j, raw12805 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12805step0 = (fun i j => raw12805 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12805step0 raw12805; decide +kernel
      have hl : raw12805step0Labels = raw12805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12805 raw12805Labels permutation265 hz
    mixedMoment B raw12805step0 raw12805step0Labels = mixedMoment B raw12805step1 raw12805step1Labels := by
      have ha : raw12805step1 = (fun i j => raw12805step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12805step1 raw12805step0; decide +kernel
      have hl : raw12805step1Labels = raw12805step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12805step0 raw12805step0Labels permutation41 permutation3
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw12806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12806 raw12806Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw12806 raw12806Labels = mixedMoment B raw12806step0 raw12806step0Labels := by
      have ha : raw12806step0 = (fun i j => raw12806 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12806step0 raw12806; decide +kernel
      have hl : raw12806step0Labels = raw12806Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12806 raw12806Labels permutation161 permutation3
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw12807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12807 raw12807Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw12807 raw12807Labels = mixedMoment B raw12807step0 raw12807step0Labels := by
      have hz : ∀ j, raw12807 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12807step0 = (fun i j => raw12807 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12807step0 raw12807; decide +kernel
      have hl : raw12807step0Labels = raw12807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12807 raw12807Labels permutation265 hz
    mixedMoment B raw12807step0 raw12807step0Labels = mixedMoment B raw12807step1 raw12807step1Labels := by
      have ha : raw12807step1 = (fun i j => raw12807step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12807step1 raw12807step0; decide +kernel
      have hl : raw12807step1Labels = raw12807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12807step0 raw12807step0Labels permutation41 permutation3
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw12808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw12808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12808 raw12808Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw12808 raw12808Labels = mixedMoment B raw12808step0 raw12808step0Labels := by
      have hz : ∀ j, raw12808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12808step0 = (fun i j => raw12808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12808step0 raw12808; decide +kernel
      have hl : raw12808step0Labels = raw12808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12808 raw12808Labels permutation265 hz
    mixedMoment B raw12808step0 raw12808step0Labels = mixedMoment B raw12808step1 raw12808step1Labels := by
      have ha : raw12808step1 = (fun i j => raw12808step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12808step1 raw12808step0; decide +kernel
      have hl : raw12808step1Labels = raw12808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12808step0 raw12808step0Labels permutation47 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw12809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12809step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12809 raw12809Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw12809 raw12809Labels = mixedMoment B raw12809step0 raw12809step0Labels := by
      have hz : ∀ j, raw12809 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12809step0 = (fun i j => raw12809 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12809step0 raw12809; decide +kernel
      have hl : raw12809step0Labels = raw12809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12809 raw12809Labels permutation590 hz
    mixedMoment B raw12809step0 raw12809step0Labels = mixedMoment B raw12809step1 raw12809step1Labels := by
      have hz : ∀ j, raw12809step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12809step1 = (fun i j => raw12809step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12809step1 raw12809step0; decide +kernel
      have hl : raw12809step1Labels = raw12809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12809step0 raw12809step0Labels permutation56 hz
    mixedMoment B raw12809step1 raw12809step1Labels = mixedMoment B raw12809step2 raw12809step2Labels := by
      have ha : raw12809step2 = (fun i j => raw12809step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12809step2 raw12809step1; decide +kernel
      have hl : raw12809step2Labels = raw12809step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12809step1 raw12809step1Labels permutation11 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw12810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12810 raw12810Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw12810 raw12810Labels = mixedMoment B raw12810step0 raw12810step0Labels := by
      have hz : ∀ j, raw12810 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12810step0 = (fun i j => raw12810 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12810step0 raw12810; decide +kernel
      have hl : raw12810step0Labels = raw12810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12810 raw12810Labels permutation265 hz
    mixedMoment B raw12810step0 raw12810step0Labels = mixedMoment B raw12810step1 raw12810step1Labels := by
      have ha : raw12810step1 = (fun i j => raw12810step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12810step1 raw12810step0; decide +kernel
      have hl : raw12810step1Labels = raw12810step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12810step0 raw12810step0Labels permutation35 permutation3
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw12811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12811 raw12811Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw12811 raw12811Labels = mixedMoment B raw12811step0 raw12811step0Labels := by
      have ha : raw12811step0 = (fun i j => raw12811 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12811step0 raw12811; decide +kernel
      have hl : raw12811step0Labels = raw12811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12811 raw12811Labels permutation155 permutation3
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw12812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12812 raw12812Labels = mixedMoment B node2638 node2638Labels := by
  calc
    mixedMoment B raw12812 raw12812Labels = mixedMoment B raw12812step0 raw12812step0Labels := by
      have hz : ∀ j, raw12812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12812step0 = (fun i j => raw12812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12812step0 raw12812; decide +kernel
      have hl : raw12812step0Labels = raw12812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12812 raw12812Labels permutation265 hz
    mixedMoment B raw12812step0 raw12812step0Labels = mixedMoment B raw12812step1 raw12812step1Labels := by
      have ha : raw12812step1 = (fun i j => raw12812step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12812step1 raw12812step0; decide +kernel
      have hl : raw12812step1Labels = raw12812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12812step0 raw12812step0Labels permutation35 permutation3
    _ = mixedMoment B node2638 node2638Labels := by rfl

def raw12813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12813 raw12813Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw12813 raw12813Labels = mixedMoment B raw12813step0 raw12813step0Labels := by
      have hz : ∀ j, raw12813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12813step0 = (fun i j => raw12813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12813step0 raw12813; decide +kernel
      have hl : raw12813step0Labels = raw12813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12813 raw12813Labels permutation265 hz
    mixedMoment B raw12813step0 raw12813step0Labels = mixedMoment B raw12813step1 raw12813step1Labels := by
      have ha : raw12813step1 = (fun i j => raw12813step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12813step1 raw12813step0; decide +kernel
      have hl : raw12813step1Labels = raw12813step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12813step0 raw12813step0Labels permutation45 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw12814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12814 raw12814Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw12814 raw12814Labels = mixedMoment B raw12814step0 raw12814step0Labels := by
      have hz : ∀ j, raw12814 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12814step0 = (fun i j => raw12814 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12814step0 raw12814; decide +kernel
      have hl : raw12814step0Labels = raw12814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12814 raw12814Labels permutation590 hz
    mixedMoment B raw12814step0 raw12814step0Labels = mixedMoment B raw12814step1 raw12814step1Labels := by
      have hz : ∀ j, raw12814step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12814step1 = (fun i j => raw12814step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12814step1 raw12814step0; decide +kernel
      have hl : raw12814step1Labels = raw12814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12814step0 raw12814step0Labels permutation56 hz
    mixedMoment B raw12814step1 raw12814step1Labels = mixedMoment B raw12814step2 raw12814step2Labels := by
      have ha : raw12814step2 = (fun i j => raw12814step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12814step2 raw12814step1; decide +kernel
      have hl : raw12814step2Labels = raw12814step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12814step1 raw12814step1Labels permutation9 permutation3
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw12815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12815 raw12815Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw12815 raw12815Labels = mixedMoment B raw12815step0 raw12815step0Labels := by
      have hz : ∀ j, raw12815 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12815step0 = (fun i j => raw12815 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12815step0 raw12815; decide +kernel
      have hl : raw12815step0Labels = raw12815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12815 raw12815Labels permutation265 hz
    mixedMoment B raw12815step0 raw12815step0Labels = mixedMoment B raw12815step1 raw12815step1Labels := by
      have ha : raw12815step1 = (fun i j => raw12815step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12815step1 raw12815step0; decide +kernel
      have hl : raw12815step1Labels = raw12815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12815step0 raw12815step0Labels permutation33 permutation3
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw12816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12816 raw12816Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw12816 raw12816Labels = mixedMoment B raw12816step0 raw12816step0Labels := by
      have ha : raw12816step0 = (fun i j => raw12816 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12816step0 raw12816; decide +kernel
      have hl : raw12816step0Labels = raw12816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12816 raw12816Labels permutation153 permutation3
    _ = mixedMoment B node2491 node2491Labels := by rfl

def raw12817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12817 raw12817Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw12817 raw12817Labels = mixedMoment B raw12817step0 raw12817step0Labels := by
      have hz : ∀ j, raw12817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12817step0 = (fun i j => raw12817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12817step0 raw12817; decide +kernel
      have hl : raw12817step0Labels = raw12817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12817 raw12817Labels permutation265 hz
    mixedMoment B raw12817step0 raw12817step0Labels = mixedMoment B raw12817step1 raw12817step1Labels := by
      have ha : raw12817step1 = (fun i j => raw12817step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12817step1 raw12817step0; decide +kernel
      have hl : raw12817step1Labels = raw12817step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12817step0 raw12817step0Labels permutation33 permutation3
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw12818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12818step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12818 raw12818Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw12818 raw12818Labels = mixedMoment B raw12818step0 raw12818step0Labels := by
      have hz : ∀ j, raw12818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12818step0 = (fun i j => raw12818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12818step0 raw12818; decide +kernel
      have hl : raw12818step0Labels = raw12818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12818 raw12818Labels permutation265 hz
    mixedMoment B raw12818step0 raw12818step0Labels = mixedMoment B raw12818step1 raw12818step1Labels := by
      have ha : raw12818step1 = (fun i j => raw12818step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12818step1 raw12818step0; decide +kernel
      have hl : raw12818step1Labels = raw12818step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12818step0 raw12818step0Labels permutation39 permutation3
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw12819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12819step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12819step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12819step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12819 raw12819Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw12819 raw12819Labels = mixedMoment B raw12819step0 raw12819step0Labels := by
      have hz : ∀ j, raw12819 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12819step0 = (fun i j => raw12819 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12819step0 raw12819; decide +kernel
      have hl : raw12819step0Labels = raw12819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12819 raw12819Labels permutation590 hz
    mixedMoment B raw12819step0 raw12819step0Labels = mixedMoment B raw12819step1 raw12819step1Labels := by
      have hz : ∀ j, raw12819step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12819step1 = (fun i j => raw12819step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12819step1 raw12819step0; decide +kernel
      have hl : raw12819step1Labels = raw12819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12819step0 raw12819step0Labels permutation56 hz
    mixedMoment B raw12819step1 raw12819step1Labels = mixedMoment B raw12819step2 raw12819step2Labels := by
      have ha : raw12819step2 = (fun i j => raw12819step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12819step2 raw12819step1; decide +kernel
      have hl : raw12819step2Labels = raw12819step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12819step1 raw12819step1Labels permutation8 permutation3
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw12820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12820 raw12820Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw12820 raw12820Labels = mixedMoment B raw12820step0 raw12820step0Labels := by
      have hz : ∀ j, raw12820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12820step0 = (fun i j => raw12820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12820step0 raw12820; decide +kernel
      have hl : raw12820step0Labels = raw12820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12820 raw12820Labels permutation265 hz
    mixedMoment B raw12820step0 raw12820step0Labels = mixedMoment B raw12820step1 raw12820step1Labels := by
      have ha : raw12820step1 = (fun i j => raw12820step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12820step1 raw12820step0; decide +kernel
      have hl : raw12820step1Labels = raw12820step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12820step0 raw12820step0Labels permutation32 permutation3
    _ = mixedMoment B node1053 node1053Labels := by rfl

def raw12821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12821 raw12821Labels = mixedMoment B node2490 node2490Labels := by
  calc
    mixedMoment B raw12821 raw12821Labels = mixedMoment B raw12821step0 raw12821step0Labels := by
      have ha : raw12821step0 = (fun i j => raw12821 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12821step0 raw12821; decide +kernel
      have hl : raw12821step0Labels = raw12821Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12821 raw12821Labels permutation152 permutation3
    _ = mixedMoment B node2490 node2490Labels := by rfl

def raw12822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12822 raw12822Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw12822 raw12822Labels = mixedMoment B raw12822step0 raw12822step0Labels := by
      have hz : ∀ j, raw12822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12822step0 = (fun i j => raw12822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12822step0 raw12822; decide +kernel
      have hl : raw12822step0Labels = raw12822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12822 raw12822Labels permutation265 hz
    mixedMoment B raw12822step0 raw12822step0Labels = mixedMoment B raw12822step1 raw12822step1Labels := by
      have ha : raw12822step1 = (fun i j => raw12822step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12822step1 raw12822step0; decide +kernel
      have hl : raw12822step1Labels = raw12822step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12822step0 raw12822step0Labels permutation32 permutation3
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw12823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12823 raw12823Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw12823 raw12823Labels = mixedMoment B raw12823step0 raw12823step0Labels := by
      have hz : ∀ j, raw12823 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12823step0 = (fun i j => raw12823 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12823step0 raw12823; decide +kernel
      have hl : raw12823step0Labels = raw12823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12823 raw12823Labels permutation265 hz
    mixedMoment B raw12823step0 raw12823step0Labels = mixedMoment B raw12823step1 raw12823step1Labels := by
      have ha : raw12823step1 = (fun i j => raw12823step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12823step1 raw12823step0; decide +kernel
      have hl : raw12823step1Labels = raw12823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12823step0 raw12823step0Labels permutation38 permutation3
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw12824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12824 raw12824Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw12824 raw12824Labels = mixedMoment B raw12824step0 raw12824step0Labels := by
      have hz : ∀ j, raw12824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12824step0 = (fun i j => raw12824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12824step0 raw12824; decide +kernel
      have hl : raw12824step0Labels = raw12824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12824 raw12824Labels permutation265 hz
    mixedMoment B raw12824step0 raw12824step0Labels = mixedMoment B raw12824step1 raw12824step1Labels := by
      have ha : raw12824step1 = (fun i j => raw12824step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12824step1 raw12824step0; decide +kernel
      have hl : raw12824step1Labels = raw12824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12824step0 raw12824step0Labels permutation44 permutation3
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw12825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12825step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12825 raw12825Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw12825 raw12825Labels = mixedMoment B raw12825step0 raw12825step0Labels := by
      have ha : raw12825step0 = (fun i j => raw12825 (permutation501 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12825step0 raw12825; decide +kernel
      have hl : raw12825step0Labels = raw12825Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12825 raw12825Labels permutation501 permutation7
    mixedMoment B raw12825step0 raw12825step0Labels = mixedMoment B raw12825step1 raw12825step1Labels := by
      have ha : raw12825step1 = raw12825step0 := by apply Matrix.ext; unfold raw12825step1 raw12825step0; decide +kernel
      have hl : raw12825step0Labels = labelEmbedding1 ∘ raw12825step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12825step0 raw12825step0Labels raw12825step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw12826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12826step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12826step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12826step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12826 raw12826Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw12826 raw12826Labels = mixedMoment B raw12826step0 raw12826step0Labels := by
      have hz : ∀ j, raw12826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12826step0 = (fun i j => raw12826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12826step0 raw12826; decide +kernel
      have hl : raw12826step0Labels = raw12826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12826 raw12826Labels permutation265 hz
    mixedMoment B raw12826step0 raw12826step0Labels = mixedMoment B raw12826step1 raw12826step1Labels := by
      have ha : raw12826step1 = (fun i j => raw12826step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12826step1 raw12826step0; decide +kernel
      have hl : raw12826step1Labels = raw12826step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12826step0 raw12826step0Labels permutation61 permutation7
    mixedMoment B raw12826step1 raw12826step1Labels = mixedMoment B raw12826step2 raw12826step2Labels := by
      have ha : raw12826step2 = -raw12826step1 := by apply Matrix.ext; change ∀ i j, raw12826step2 i j = -(raw12826step1 i j); unfold raw12826step2 raw12826step1; decide +kernel
      have hl : raw12826step2Labels = raw12826step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12826step2 raw12826step2Labels = mixedMoment B raw12826step3 raw12826step3Labels := by
      have ha : raw12826step3 = raw12826step2 := by apply Matrix.ext; unfold raw12826step3 raw12826step2; decide +kernel
      have hl : raw12826step2Labels = labelEmbedding1 ∘ raw12826step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12826step2 raw12826step2Labels raw12826step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw12827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12827step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12827step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12827 raw12827Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw12827 raw12827Labels = mixedMoment B raw12827step0 raw12827step0Labels := by
      have hz : ∀ j, raw12827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12827step0 = (fun i j => raw12827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12827step0 raw12827; decide +kernel
      have hl : raw12827step0Labels = raw12827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12827 raw12827Labels permutation265 hz
    mixedMoment B raw12827step0 raw12827step0Labels = mixedMoment B raw12827step1 raw12827step1Labels := by
      have ha : raw12827step1 = (fun i j => raw12827step0 (permutation83 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12827step1 raw12827step0; decide +kernel
      have hl : raw12827step1Labels = raw12827step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12827step0 raw12827step0Labels permutation83 permutation5
    mixedMoment B raw12827step1 raw12827step1Labels = mixedMoment B raw12827step2 raw12827step2Labels := by
      have ha : raw12827step2 = -raw12827step1 := by apply Matrix.ext; change ∀ i j, raw12827step2 i j = -(raw12827step1 i j); unfold raw12827step2 raw12827step1; decide +kernel
      have hl : raw12827step2Labels = raw12827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12827step2 raw12827step2Labels = mixedMoment B raw12827step3 raw12827step3Labels := by
      have ha : raw12827step3 = raw12827step2 := by apply Matrix.ext; unfold raw12827step3 raw12827step2; decide +kernel
      have hl : raw12827step2Labels = labelEmbedding1 ∘ raw12827step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12827step2 raw12827step2Labels raw12827step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw12828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12828 raw12828Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw12828 raw12828Labels = mixedMoment B raw12828step0 raw12828step0Labels := by
      have hz : ∀ j, raw12828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12828step0 = (fun i j => raw12828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12828step0 raw12828; decide +kernel
      have hl : raw12828step0Labels = raw12828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12828 raw12828Labels permutation265 hz
    mixedMoment B raw12828step0 raw12828step0Labels = mixedMoment B raw12828step1 raw12828step1Labels := by
      have ha : raw12828step1 = (fun i j => raw12828step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12828step1 raw12828step0; decide +kernel
      have hl : raw12828step1Labels = raw12828step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12828step0 raw12828step0Labels permutation96 permutation7
    mixedMoment B raw12828step1 raw12828step1Labels = mixedMoment B raw12828step2 raw12828step2Labels := by
      have ha : raw12828step2 = raw12828step1 := by apply Matrix.ext; unfold raw12828step2 raw12828step1; decide +kernel
      have hl : raw12828step1Labels = labelEmbedding1 ∘ raw12828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12828step1 raw12828step1Labels raw12828step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw12829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12829 raw12829Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw12829 raw12829Labels = mixedMoment B raw12829step0 raw12829step0Labels := by
      have hz : ∀ j, raw12829 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12829step0 = (fun i j => raw12829 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12829step0 raw12829; decide +kernel
      have hl : raw12829step0Labels = raw12829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12829 raw12829Labels permutation590 hz
    mixedMoment B raw12829step0 raw12829step0Labels = mixedMoment B raw12829step1 raw12829step1Labels := by
      have hz : ∀ j, raw12829step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12829step1 = (fun i j => raw12829step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12829step1 raw12829step0; decide +kernel
      have hl : raw12829step1Labels = raw12829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12829step0 raw12829step0Labels permutation56 hz
    mixedMoment B raw12829step1 raw12829step1Labels = mixedMoment B raw12829step2 raw12829step2Labels := by
      have ha : raw12829step2 = (fun i j => raw12829step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12829step2 raw12829step1; decide +kernel
      have hl : raw12829step2Labels = raw12829step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12829step1 raw12829step1Labels permutation24 permutation7
    mixedMoment B raw12829step2 raw12829step2Labels = mixedMoment B raw12829step3 raw12829step3Labels := by
      have ha : raw12829step3 = raw12829step2 := by apply Matrix.ext; unfold raw12829step3 raw12829step2; decide +kernel
      have hl : raw12829step2Labels = labelEmbedding1 ∘ raw12829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12829step2 raw12829step2Labels raw12829step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw12830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12830step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12830 raw12830Labels = mixedMoment B node1638 node1638Labels := by
  calc
    mixedMoment B raw12830 raw12830Labels = mixedMoment B raw12830step0 raw12830step0Labels := by
      have ha : raw12830step0 = (fun i j => raw12830 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12830step0 raw12830; decide +kernel
      have hl : raw12830step0Labels = raw12830Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12830 raw12830Labels permutation213 permutation5
    mixedMoment B raw12830step0 raw12830step0Labels = mixedMoment B raw12830step1 raw12830step1Labels := by
      have ha : raw12830step1 = -raw12830step0 := by apply Matrix.ext; change ∀ i j, raw12830step1 i j = -(raw12830step0 i j); unfold raw12830step1 raw12830step0; decide +kernel
      have hl : raw12830step1Labels = raw12830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12830step1 raw12830step1Labels = mixedMoment B raw12830step2 raw12830step2Labels := by
      have ha : raw12830step2 = raw12830step1 := by apply Matrix.ext; unfold raw12830step2 raw12830step1; decide +kernel
      have hl : raw12830step1Labels = labelEmbedding1 ∘ raw12830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12830step1 raw12830step1Labels raw12830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1638 node1638Labels := by rfl

def raw12831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12831step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12831step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12831step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12831step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12831 raw12831Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw12831 raw12831Labels = mixedMoment B raw12831step0 raw12831step0Labels := by
      have ha : raw12831step0 = (fun i j => raw12831 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12831step0 raw12831; decide +kernel
      have hl : raw12831step0Labels = raw12831Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12831 raw12831Labels permutation214 permutation5
    mixedMoment B raw12831step0 raw12831step0Labels = mixedMoment B raw12831step1 raw12831step1Labels := by
      have ha : raw12831step1 = -raw12831step0 := by apply Matrix.ext; change ∀ i j, raw12831step1 i j = -(raw12831step0 i j); unfold raw12831step1 raw12831step0; decide +kernel
      have hl : raw12831step1Labels = raw12831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12831step1 raw12831step1Labels = mixedMoment B raw12831step2 raw12831step2Labels := by
      have ha : raw12831step2 = raw12831step1 := by apply Matrix.ext; unfold raw12831step2 raw12831step1; decide +kernel
      have hl : raw12831step1Labels = labelEmbedding1 ∘ raw12831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12831step1 raw12831step1Labels raw12831step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw12832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12832step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12832 raw12832Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw12832 raw12832Labels = mixedMoment B raw12832step0 raw12832step0Labels := by
      have ha : raw12832step0 = (fun i j => raw12832 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12832step0 raw12832; decide +kernel
      have hl : raw12832step0Labels = raw12832Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12832 raw12832Labels permutation213 permutation5
    mixedMoment B raw12832step0 raw12832step0Labels = mixedMoment B raw12832step1 raw12832step1Labels := by
      have ha : raw12832step1 = -raw12832step0 := by apply Matrix.ext; change ∀ i j, raw12832step1 i j = -(raw12832step0 i j); unfold raw12832step1 raw12832step0; decide +kernel
      have hl : raw12832step1Labels = raw12832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12832step1 raw12832step1Labels = mixedMoment B raw12832step2 raw12832step2Labels := by
      have ha : raw12832step2 = raw12832step1 := by apply Matrix.ext; unfold raw12832step2 raw12832step1; decide +kernel
      have hl : raw12832step1Labels = labelEmbedding1 ∘ raw12832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12832step1 raw12832step1Labels raw12832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw12833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12833 raw12833Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw12833 raw12833Labels = mixedMoment B raw12833step0 raw12833step0Labels := by
      have ha : raw12833step0 = (fun i j => raw12833 (permutation235 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12833step0 raw12833; decide +kernel
      have hl : raw12833step0Labels = raw12833Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12833 raw12833Labels permutation235 permutation5
    mixedMoment B raw12833step0 raw12833step0Labels = mixedMoment B raw12833step1 raw12833step1Labels := by
      have ha : raw12833step1 = -raw12833step0 := by apply Matrix.ext; change ∀ i j, raw12833step1 i j = -(raw12833step0 i j); unfold raw12833step1 raw12833step0; decide +kernel
      have hl : raw12833step1Labels = raw12833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12833step1 raw12833step1Labels = mixedMoment B raw12833step2 raw12833step2Labels := by
      have ha : raw12833step2 = raw12833step1 := by apply Matrix.ext; unfold raw12833step2 raw12833step1; decide +kernel
      have hl : raw12833step1Labels = labelEmbedding1 ∘ raw12833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12833step1 raw12833step1Labels raw12833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw12834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12834step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12834step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12834step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12834 raw12834Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12834 raw12834Labels = mixedMoment B raw12834step0 raw12834step0Labels := by
      have hz : ∀ j, raw12834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12834step0 = (fun i j => raw12834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12834step0 raw12834; decide +kernel
      have hl : raw12834step0Labels = raw12834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12834 raw12834Labels permutation590 hz
    mixedMoment B raw12834step0 raw12834step0Labels = mixedMoment B raw12834step1 raw12834step1Labels := by
      have ha : raw12834step1 = (fun i j => raw12834step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12834step1 raw12834step0; decide +kernel
      have hl : raw12834step1Labels = raw12834step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12834step0 raw12834step0Labels permutation48 permutation5
    mixedMoment B raw12834step1 raw12834step1Labels = mixedMoment B raw12834step2 raw12834step2Labels := by
      have ha : raw12834step2 = -raw12834step1 := by apply Matrix.ext; change ∀ i j, raw12834step2 i j = -(raw12834step1 i j); unfold raw12834step2 raw12834step1; decide +kernel
      have hl : raw12834step2Labels = raw12834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12834step2 raw12834step2Labels = mixedMoment B raw12834step3 raw12834step3Labels := by
      have ha : raw12834step3 = raw12834step2 := by apply Matrix.ext; unfold raw12834step3 raw12834step2; decide +kernel
      have hl : raw12834step2Labels = labelEmbedding1 ∘ raw12834step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12834step2 raw12834step2Labels raw12834step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw12835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw12835step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12835step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw12835step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12835 raw12835Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw12835 raw12835Labels = mixedMoment B raw12835step0 raw12835step0Labels := by
      have hz : ∀ j, raw12835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12835step0 = (fun i j => raw12835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12835step0 raw12835; decide +kernel
      have hl : raw12835step0Labels = raw12835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12835 raw12835Labels permutation265 hz
    mixedMoment B raw12835step0 raw12835step0Labels = mixedMoment B raw12835step1 raw12835step1Labels := by
      have ha : raw12835step1 = (fun i j => raw12835step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12835step1 raw12835step0; decide +kernel
      have hl : raw12835step1Labels = raw12835step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12835step0 raw12835step0Labels permutation41 permutation5
    mixedMoment B raw12835step1 raw12835step1Labels = mixedMoment B raw12835step2 raw12835step2Labels := by
      have ha : raw12835step2 = -raw12835step1 := by apply Matrix.ext; change ∀ i j, raw12835step2 i j = -(raw12835step1 i j); unfold raw12835step2 raw12835step1; decide +kernel
      have hl : raw12835step2Labels = raw12835step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12835step2 raw12835step2Labels = mixedMoment B raw12835step3 raw12835step3Labels := by
      have ha : raw12835step3 = raw12835step2 := by apply Matrix.ext; unfold raw12835step3 raw12835step2; decide +kernel
      have hl : raw12835step2Labels = labelEmbedding1 ∘ raw12835step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12835step2 raw12835step2Labels raw12835step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw12836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12836 raw12836Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw12836 raw12836Labels = mixedMoment B raw12836step0 raw12836step0Labels := by
      have ha : raw12836step0 = (fun i j => raw12836 (permutation433 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12836step0 raw12836; decide +kernel
      have hl : raw12836step0Labels = raw12836Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12836 raw12836Labels permutation433 permutation5
    mixedMoment B raw12836step0 raw12836step0Labels = mixedMoment B raw12836step1 raw12836step1Labels := by
      have ha : raw12836step1 = raw12836step0 := by apply Matrix.ext; unfold raw12836step1 raw12836step0; decide +kernel
      have hl : raw12836step0Labels = labelEmbedding1 ∘ raw12836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12836step0 raw12836step0Labels raw12836step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw12837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12837 raw12837Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw12837 raw12837Labels = mixedMoment B raw12837step0 raw12837step0Labels := by
      have hz : ∀ j, raw12837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12837step0 = (fun i j => raw12837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12837step0 raw12837; decide +kernel
      have hl : raw12837step0Labels = raw12837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12837 raw12837Labels permutation265 hz
    mixedMoment B raw12837step0 raw12837step0Labels = mixedMoment B raw12837step1 raw12837step1Labels := by
      have ha : raw12837step1 = (fun i j => raw12837step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12837step1 raw12837step0; decide +kernel
      have hl : raw12837step1Labels = raw12837step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12837step0 raw12837step0Labels permutation79 permutation5
    mixedMoment B raw12837step1 raw12837step1Labels = mixedMoment B raw12837step2 raw12837step2Labels := by
      have ha : raw12837step2 = raw12837step1 := by apply Matrix.ext; unfold raw12837step2 raw12837step1; decide +kernel
      have hl : raw12837step1Labels = labelEmbedding1 ∘ raw12837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12837step1 raw12837step1Labels raw12837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw12838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12838 raw12838Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw12838 raw12838Labels = mixedMoment B raw12838step0 raw12838step0Labels := by
      have hz : ∀ j, raw12838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12838step0 = (fun i j => raw12838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12838step0 raw12838; decide +kernel
      have hl : raw12838step0Labels = raw12838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12838 raw12838Labels permutation265 hz
    mixedMoment B raw12838step0 raw12838step0Labels = mixedMoment B raw12838step1 raw12838step1Labels := by
      have ha : raw12838step1 = (fun i j => raw12838step0 (permutation77 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12838step1 raw12838step0; decide +kernel
      have hl : raw12838step1Labels = raw12838step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12838step0 raw12838step0Labels permutation77 permutation5
    mixedMoment B raw12838step1 raw12838step1Labels = mixedMoment B raw12838step2 raw12838step2Labels := by
      have ha : raw12838step2 = raw12838step1 := by apply Matrix.ext; unfold raw12838step2 raw12838step1; decide +kernel
      have hl : raw12838step1Labels = labelEmbedding1 ∘ raw12838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12838step1 raw12838step1Labels raw12838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw12839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12839step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12839step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12839step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12839 raw12839Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw12839 raw12839Labels = mixedMoment B raw12839step0 raw12839step0Labels := by
      have hz : ∀ j, raw12839 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12839step0 = (fun i j => raw12839 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12839step0 raw12839; decide +kernel
      have hl : raw12839step0Labels = raw12839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12839 raw12839Labels permutation590 hz
    mixedMoment B raw12839step0 raw12839step0Labels = mixedMoment B raw12839step1 raw12839step1Labels := by
      have hz : ∀ j, raw12839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12839step1 = (fun i j => raw12839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12839step1 raw12839step0; decide +kernel
      have hl : raw12839step1Labels = raw12839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12839step0 raw12839step0Labels permutation56 hz
    mixedMoment B raw12839step1 raw12839step1Labels = mixedMoment B raw12839step2 raw12839step2Labels := by
      have ha : raw12839step2 = (fun i j => raw12839step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12839step2 raw12839step1; decide +kernel
      have hl : raw12839step2Labels = raw12839step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12839step1 raw12839step1Labels permutation19 permutation5
    mixedMoment B raw12839step2 raw12839step2Labels = mixedMoment B raw12839step3 raw12839step3Labels := by
      have ha : raw12839step3 = raw12839step2 := by apply Matrix.ext; unfold raw12839step3 raw12839step2; decide +kernel
      have hl : raw12839step2Labels = labelEmbedding1 ∘ raw12839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12839step2 raw12839step2Labels raw12839step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw12840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12840 raw12840Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw12840 raw12840Labels = mixedMoment B raw12840step0 raw12840step0Labels := by
      have hz : ∀ j, raw12840 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12840step0 = (fun i j => raw12840 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12840step0 raw12840; decide +kernel
      have hl : raw12840step0Labels = raw12840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12840 raw12840Labels permutation265 hz
    mixedMoment B raw12840step0 raw12840step0Labels = mixedMoment B raw12840step1 raw12840step1Labels := by
      have ha : raw12840step1 = (fun i j => raw12840step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12840step1 raw12840step0; decide +kernel
      have hl : raw12840step1Labels = raw12840step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12840step0 raw12840step0Labels permutation47 permutation5
    mixedMoment B raw12840step1 raw12840step1Labels = mixedMoment B raw12840step2 raw12840step2Labels := by
      have ha : raw12840step2 = -raw12840step1 := by apply Matrix.ext; change ∀ i j, raw12840step2 i j = -(raw12840step1 i j); unfold raw12840step2 raw12840step1; decide +kernel
      have hl : raw12840step2Labels = raw12840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12840step2 raw12840step2Labels = mixedMoment B raw12840step3 raw12840step3Labels := by
      have ha : raw12840step3 = raw12840step2 := by apply Matrix.ext; unfold raw12840step3 raw12840step2; decide +kernel
      have hl : raw12840step2Labels = labelEmbedding1 ∘ raw12840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12840step2 raw12840step2Labels raw12840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw12841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12841 raw12841Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw12841 raw12841Labels = mixedMoment B raw12841step0 raw12841step0Labels := by
      have ha : raw12841step0 = (fun i j => raw12841 (permutation167 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12841step0 raw12841; decide +kernel
      have hl : raw12841step0Labels = raw12841Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12841 raw12841Labels permutation167 permutation5
    mixedMoment B raw12841step0 raw12841step0Labels = mixedMoment B raw12841step1 raw12841step1Labels := by
      have ha : raw12841step1 = -raw12841step0 := by apply Matrix.ext; change ∀ i j, raw12841step1 i j = -(raw12841step0 i j); unfold raw12841step1 raw12841step0; decide +kernel
      have hl : raw12841step1Labels = raw12841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12841step1 raw12841step1Labels = mixedMoment B raw12841step2 raw12841step2Labels := by
      have ha : raw12841step2 = raw12841step1 := by apply Matrix.ext; unfold raw12841step2 raw12841step1; decide +kernel
      have hl : raw12841step1Labels = labelEmbedding1 ∘ raw12841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12841step1 raw12841step1Labels raw12841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw12842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw12842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12842step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12842 raw12842Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw12842 raw12842Labels = mixedMoment B raw12842step0 raw12842step0Labels := by
      have hz : ∀ j, raw12842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12842step0 = (fun i j => raw12842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12842step0 raw12842; decide +kernel
      have hl : raw12842step0Labels = raw12842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12842 raw12842Labels permutation265 hz
    mixedMoment B raw12842step0 raw12842step0Labels = mixedMoment B raw12842step1 raw12842step1Labels := by
      have ha : raw12842step1 = (fun i j => raw12842step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12842step1 raw12842step0; decide +kernel
      have hl : raw12842step1Labels = raw12842step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12842step0 raw12842step0Labels permutation46 permutation5
    mixedMoment B raw12842step1 raw12842step1Labels = mixedMoment B raw12842step2 raw12842step2Labels := by
      have ha : raw12842step2 = -raw12842step1 := by apply Matrix.ext; change ∀ i j, raw12842step2 i j = -(raw12842step1 i j); unfold raw12842step2 raw12842step1; decide +kernel
      have hl : raw12842step2Labels = raw12842step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12842step2 raw12842step2Labels = mixedMoment B raw12842step3 raw12842step3Labels := by
      have ha : raw12842step3 = raw12842step2 := by apply Matrix.ext; unfold raw12842step3 raw12842step2; decide +kernel
      have hl : raw12842step2Labels = labelEmbedding1 ∘ raw12842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12842step2 raw12842step2Labels raw12842step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw12843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12843step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12843step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12843step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12843step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12843 raw12843Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw12843 raw12843Labels = mixedMoment B raw12843step0 raw12843step0Labels := by
      have hz : ∀ j, raw12843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12843step0 = (fun i j => raw12843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12843step0 raw12843; decide +kernel
      have hl : raw12843step0Labels = raw12843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12843 raw12843Labels permutation265 hz
    mixedMoment B raw12843step0 raw12843step0Labels = mixedMoment B raw12843step1 raw12843step1Labels := by
      have ha : raw12843step1 = (fun i j => raw12843step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12843step1 raw12843step0; decide +kernel
      have hl : raw12843step1Labels = raw12843step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12843step0 raw12843step0Labels permutation47 permutation5
    mixedMoment B raw12843step1 raw12843step1Labels = mixedMoment B raw12843step2 raw12843step2Labels := by
      have ha : raw12843step2 = -raw12843step1 := by apply Matrix.ext; change ∀ i j, raw12843step2 i j = -(raw12843step1 i j); unfold raw12843step2 raw12843step1; decide +kernel
      have hl : raw12843step2Labels = raw12843step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12843step2 raw12843step2Labels = mixedMoment B raw12843step3 raw12843step3Labels := by
      have ha : raw12843step3 = raw12843step2 := by apply Matrix.ext; unfold raw12843step3 raw12843step2; decide +kernel
      have hl : raw12843step2Labels = labelEmbedding1 ∘ raw12843step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12843step2 raw12843step2Labels raw12843step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw12844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12844step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12844step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12844step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw12844step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12844step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw12844step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12844step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw12844step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12844 raw12844Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw12844 raw12844Labels = mixedMoment B raw12844step0 raw12844step0Labels := by
      have hz : ∀ j, raw12844 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12844step0 = (fun i j => raw12844 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12844step0 raw12844; decide +kernel
      have hl : raw12844step0Labels = raw12844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12844 raw12844Labels permutation590 hz
    mixedMoment B raw12844step0 raw12844step0Labels = mixedMoment B raw12844step1 raw12844step1Labels := by
      have hz : ∀ j, raw12844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12844step1 = (fun i j => raw12844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12844step1 raw12844step0; decide +kernel
      have hl : raw12844step1Labels = raw12844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12844step0 raw12844step0Labels permutation56 hz
    mixedMoment B raw12844step1 raw12844step1Labels = mixedMoment B raw12844step2 raw12844step2Labels := by
      have ha : raw12844step2 = (fun i j => raw12844step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12844step2 raw12844step1; decide +kernel
      have hl : raw12844step2Labels = raw12844step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12844step1 raw12844step1Labels permutation13 permutation5
    mixedMoment B raw12844step2 raw12844step2Labels = mixedMoment B raw12844step3 raw12844step3Labels := by
      have ha : raw12844step3 = -raw12844step2 := by apply Matrix.ext; change ∀ i j, raw12844step3 i j = -(raw12844step2 i j); unfold raw12844step3 raw12844step2; decide +kernel
      have hl : raw12844step3Labels = raw12844step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12844step3 raw12844step3Labels = mixedMoment B raw12844step4 raw12844step4Labels := by
      have ha : raw12844step4 = raw12844step3 := by apply Matrix.ext; unfold raw12844step4 raw12844step3; decide +kernel
      have hl : raw12844step3Labels = labelEmbedding1 ∘ raw12844step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12844step3 raw12844step3Labels raw12844step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw12845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12845step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12845 raw12845Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw12845 raw12845Labels = mixedMoment B raw12845step0 raw12845step0Labels := by
      have hz : ∀ j, raw12845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12845step0 = (fun i j => raw12845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12845step0 raw12845; decide +kernel
      have hl : raw12845step0Labels = raw12845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12845 raw12845Labels permutation265 hz
    mixedMoment B raw12845step0 raw12845step0Labels = mixedMoment B raw12845step1 raw12845step1Labels := by
      have ha : raw12845step1 = (fun i j => raw12845step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12845step1 raw12845step0; decide +kernel
      have hl : raw12845step1Labels = raw12845step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12845step0 raw12845step0Labels permutation43 permutation5
    mixedMoment B raw12845step1 raw12845step1Labels = mixedMoment B raw12845step2 raw12845step2Labels := by
      have ha : raw12845step2 = -raw12845step1 := by apply Matrix.ext; change ∀ i j, raw12845step2 i j = -(raw12845step1 i j); unfold raw12845step2 raw12845step1; decide +kernel
      have hl : raw12845step2Labels = raw12845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12845step2 raw12845step2Labels = mixedMoment B raw12845step3 raw12845step3Labels := by
      have ha : raw12845step3 = raw12845step2 := by apply Matrix.ext; unfold raw12845step3 raw12845step2; decide +kernel
      have hl : raw12845step2Labels = labelEmbedding1 ∘ raw12845step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12845step2 raw12845step2Labels raw12845step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1649 node1649Labels := by rfl

def raw12846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12846 raw12846Labels = mixedMoment B node3447 node3447Labels := by
  calc
    mixedMoment B raw12846 raw12846Labels = mixedMoment B raw12846step0 raw12846step0Labels := by
      have ha : raw12846step0 = (fun i j => raw12846 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12846step0 raw12846; decide +kernel
      have hl : raw12846step0Labels = raw12846Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12846 raw12846Labels permutation163 permutation5
    mixedMoment B raw12846step0 raw12846step0Labels = mixedMoment B raw12846step1 raw12846step1Labels := by
      have ha : raw12846step1 = -raw12846step0 := by apply Matrix.ext; change ∀ i j, raw12846step1 i j = -(raw12846step0 i j); unfold raw12846step1 raw12846step0; decide +kernel
      have hl : raw12846step1Labels = raw12846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12846step1 raw12846step1Labels = mixedMoment B raw12846step2 raw12846step2Labels := by
      have ha : raw12846step2 = raw12846step1 := by apply Matrix.ext; unfold raw12846step2 raw12846step1; decide +kernel
      have hl : raw12846step1Labels = labelEmbedding1 ∘ raw12846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12846step1 raw12846step1Labels raw12846step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3447 node3447Labels := by rfl

def raw12847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12847step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw12847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12847step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12847step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12847 raw12847Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw12847 raw12847Labels = mixedMoment B raw12847step0 raw12847step0Labels := by
      have hz : ∀ j, raw12847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12847step0 = (fun i j => raw12847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12847step0 raw12847; decide +kernel
      have hl : raw12847step0Labels = raw12847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12847 raw12847Labels permutation265 hz
    mixedMoment B raw12847step0 raw12847step0Labels = mixedMoment B raw12847step1 raw12847step1Labels := by
      have ha : raw12847step1 = (fun i j => raw12847step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12847step1 raw12847step0; decide +kernel
      have hl : raw12847step1Labels = raw12847step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12847step0 raw12847step0Labels permutation39 permutation5
    mixedMoment B raw12847step1 raw12847step1Labels = mixedMoment B raw12847step2 raw12847step2Labels := by
      have ha : raw12847step2 = -raw12847step1 := by apply Matrix.ext; change ∀ i j, raw12847step2 i j = -(raw12847step1 i j); unfold raw12847step2 raw12847step1; decide +kernel
      have hl : raw12847step2Labels = raw12847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12847step2 raw12847step2Labels = mixedMoment B raw12847step3 raw12847step3Labels := by
      have ha : raw12847step3 = raw12847step2 := by apply Matrix.ext; unfold raw12847step3 raw12847step2; decide +kernel
      have hl : raw12847step2Labels = labelEmbedding1 ∘ raw12847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12847step2 raw12847step2Labels raw12847step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw12848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12848step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12848step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12848step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12848step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12848 raw12848Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw12848 raw12848Labels = mixedMoment B raw12848step0 raw12848step0Labels := by
      have hz : ∀ j, raw12848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12848step0 = (fun i j => raw12848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12848step0 raw12848; decide +kernel
      have hl : raw12848step0Labels = raw12848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12848 raw12848Labels permutation265 hz
    mixedMoment B raw12848step0 raw12848step0Labels = mixedMoment B raw12848step1 raw12848step1Labels := by
      have ha : raw12848step1 = (fun i j => raw12848step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12848step1 raw12848step0; decide +kernel
      have hl : raw12848step1Labels = raw12848step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12848step0 raw12848step0Labels permutation43 permutation5
    mixedMoment B raw12848step1 raw12848step1Labels = mixedMoment B raw12848step2 raw12848step2Labels := by
      have ha : raw12848step2 = -raw12848step1 := by apply Matrix.ext; change ∀ i j, raw12848step2 i j = -(raw12848step1 i j); unfold raw12848step2 raw12848step1; decide +kernel
      have hl : raw12848step2Labels = raw12848step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12848step2 raw12848step2Labels = mixedMoment B raw12848step3 raw12848step3Labels := by
      have ha : raw12848step3 = raw12848step2 := by apply Matrix.ext; unfold raw12848step3 raw12848step2; decide +kernel
      have hl : raw12848step2Labels = labelEmbedding1 ∘ raw12848step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12848step2 raw12848step2Labels raw12848step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw12849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12849step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12849step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12849step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12849step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12849step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12849step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12849step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12849 raw12849Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw12849 raw12849Labels = mixedMoment B raw12849step0 raw12849step0Labels := by
      have hz : ∀ j, raw12849 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12849step0 = (fun i j => raw12849 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12849step0 raw12849; decide +kernel
      have hl : raw12849step0Labels = raw12849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12849 raw12849Labels permutation590 hz
    mixedMoment B raw12849step0 raw12849step0Labels = mixedMoment B raw12849step1 raw12849step1Labels := by
      have hz : ∀ j, raw12849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12849step1 = (fun i j => raw12849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12849step1 raw12849step0; decide +kernel
      have hl : raw12849step1Labels = raw12849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12849step0 raw12849step0Labels permutation56 hz
    mixedMoment B raw12849step1 raw12849step1Labels = mixedMoment B raw12849step2 raw12849step2Labels := by
      have ha : raw12849step2 = (fun i j => raw12849step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12849step2 raw12849step1; decide +kernel
      have hl : raw12849step2Labels = raw12849step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12849step1 raw12849step1Labels permutation11 permutation5
    mixedMoment B raw12849step2 raw12849step2Labels = mixedMoment B raw12849step3 raw12849step3Labels := by
      have ha : raw12849step3 = -raw12849step2 := by apply Matrix.ext; change ∀ i j, raw12849step3 i j = -(raw12849step2 i j); unfold raw12849step3 raw12849step2; decide +kernel
      have hl : raw12849step3Labels = raw12849step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12849step3 raw12849step3Labels = mixedMoment B raw12849step4 raw12849step4Labels := by
      have ha : raw12849step4 = raw12849step3 := by apply Matrix.ext; unfold raw12849step4 raw12849step3; decide +kernel
      have hl : raw12849step3Labels = labelEmbedding1 ∘ raw12849step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12849step3 raw12849step3Labels raw12849step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw12850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12850 raw12850Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw12850 raw12850Labels = mixedMoment B raw12850step0 raw12850step0Labels := by
      have hz : ∀ j, raw12850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12850step0 = (fun i j => raw12850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12850step0 raw12850; decide +kernel
      have hl : raw12850step0Labels = raw12850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12850 raw12850Labels permutation265 hz
    mixedMoment B raw12850step0 raw12850step0Labels = mixedMoment B raw12850step1 raw12850step1Labels := by
      have ha : raw12850step1 = (fun i j => raw12850step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12850step1 raw12850step0; decide +kernel
      have hl : raw12850step1Labels = raw12850step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12850step0 raw12850step0Labels permutation40 permutation5
    mixedMoment B raw12850step1 raw12850step1Labels = mixedMoment B raw12850step2 raw12850step2Labels := by
      have ha : raw12850step2 = -raw12850step1 := by apply Matrix.ext; change ∀ i j, raw12850step2 i j = -(raw12850step1 i j); unfold raw12850step2 raw12850step1; decide +kernel
      have hl : raw12850step2Labels = raw12850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12850step2 raw12850step2Labels = mixedMoment B raw12850step3 raw12850step3Labels := by
      have ha : raw12850step3 = raw12850step2 := by apply Matrix.ext; unfold raw12850step3 raw12850step2; decide +kernel
      have hl : raw12850step2Labels = labelEmbedding1 ∘ raw12850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12850step2 raw12850step2Labels raw12850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw12851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12851 raw12851Labels = mixedMoment B node3441 node3441Labels := by
  calc
    mixedMoment B raw12851 raw12851Labels = mixedMoment B raw12851step0 raw12851step0Labels := by
      have ha : raw12851step0 = (fun i j => raw12851 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12851step0 raw12851; decide +kernel
      have hl : raw12851step0Labels = raw12851Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12851 raw12851Labels permutation160 permutation5
    mixedMoment B raw12851step0 raw12851step0Labels = mixedMoment B raw12851step1 raw12851step1Labels := by
      have ha : raw12851step1 = -raw12851step0 := by apply Matrix.ext; change ∀ i j, raw12851step1 i j = -(raw12851step0 i j); unfold raw12851step1 raw12851step0; decide +kernel
      have hl : raw12851step1Labels = raw12851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12851step1 raw12851step1Labels = mixedMoment B raw12851step2 raw12851step2Labels := by
      have ha : raw12851step2 = raw12851step1 := by apply Matrix.ext; unfold raw12851step2 raw12851step1; decide +kernel
      have hl : raw12851step1Labels = labelEmbedding1 ∘ raw12851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12851step1 raw12851step1Labels raw12851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3441 node3441Labels := by rfl

def raw12852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12852step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw12852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12852step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12852step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12852step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12852 raw12852Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw12852 raw12852Labels = mixedMoment B raw12852step0 raw12852step0Labels := by
      have hz : ∀ j, raw12852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12852step0 = (fun i j => raw12852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12852step0 raw12852; decide +kernel
      have hl : raw12852step0Labels = raw12852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12852 raw12852Labels permutation265 hz
    mixedMoment B raw12852step0 raw12852step0Labels = mixedMoment B raw12852step1 raw12852step1Labels := by
      have ha : raw12852step1 = (fun i j => raw12852step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12852step1 raw12852step0; decide +kernel
      have hl : raw12852step1Labels = raw12852step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12852step0 raw12852step0Labels permutation40 permutation5
    mixedMoment B raw12852step1 raw12852step1Labels = mixedMoment B raw12852step2 raw12852step2Labels := by
      have ha : raw12852step2 = -raw12852step1 := by apply Matrix.ext; change ∀ i j, raw12852step2 i j = -(raw12852step1 i j); unfold raw12852step2 raw12852step1; decide +kernel
      have hl : raw12852step2Labels = raw12852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12852step2 raw12852step2Labels = mixedMoment B raw12852step3 raw12852step3Labels := by
      have ha : raw12852step3 = raw12852step2 := by apply Matrix.ext; unfold raw12852step3 raw12852step2; decide +kernel
      have hl : raw12852step2Labels = labelEmbedding1 ∘ raw12852step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12852step2 raw12852step2Labels raw12852step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw12853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12853step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12853step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12853step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12853 raw12853Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw12853 raw12853Labels = mixedMoment B raw12853step0 raw12853step0Labels := by
      have hz : ∀ j, raw12853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12853step0 = (fun i j => raw12853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12853step0 raw12853; decide +kernel
      have hl : raw12853step0Labels = raw12853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12853 raw12853Labels permutation265 hz
    mixedMoment B raw12853step0 raw12853step0Labels = mixedMoment B raw12853step1 raw12853step1Labels := by
      have ha : raw12853step1 = (fun i j => raw12853step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12853step1 raw12853step0; decide +kernel
      have hl : raw12853step1Labels = raw12853step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12853step0 raw12853step0Labels permutation40 permutation5
    mixedMoment B raw12853step1 raw12853step1Labels = mixedMoment B raw12853step2 raw12853step2Labels := by
      have ha : raw12853step2 = -raw12853step1 := by apply Matrix.ext; change ∀ i j, raw12853step2 i j = -(raw12853step1 i j); unfold raw12853step2 raw12853step1; decide +kernel
      have hl : raw12853step2Labels = raw12853step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12853step2 raw12853step2Labels = mixedMoment B raw12853step3 raw12853step3Labels := by
      have ha : raw12853step3 = raw12853step2 := by apply Matrix.ext; unfold raw12853step3 raw12853step2; decide +kernel
      have hl : raw12853step2Labels = labelEmbedding1 ∘ raw12853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12853step2 raw12853step2Labels raw12853step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw12854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12854step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw12854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12854step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12854step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw12854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12854 raw12854Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw12854 raw12854Labels = mixedMoment B raw12854step0 raw12854step0Labels := by
      have hz : ∀ j, raw12854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12854step0 = (fun i j => raw12854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12854step0 raw12854; decide +kernel
      have hl : raw12854step0Labels = raw12854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12854 raw12854Labels permutation265 hz
    mixedMoment B raw12854step0 raw12854step0Labels = mixedMoment B raw12854step1 raw12854step1Labels := by
      have ha : raw12854step1 = (fun i j => raw12854step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12854step1 raw12854step0; decide +kernel
      have hl : raw12854step1Labels = raw12854step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12854step0 raw12854step0Labels permutation46 permutation5
    mixedMoment B raw12854step1 raw12854step1Labels = mixedMoment B raw12854step2 raw12854step2Labels := by
      have ha : raw12854step2 = -raw12854step1 := by apply Matrix.ext; change ∀ i j, raw12854step2 i j = -(raw12854step1 i j); unfold raw12854step2 raw12854step1; decide +kernel
      have hl : raw12854step2Labels = raw12854step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12854step2 raw12854step2Labels = mixedMoment B raw12854step3 raw12854step3Labels := by
      have ha : raw12854step3 = raw12854step2 := by apply Matrix.ext; unfold raw12854step3 raw12854step2; decide +kernel
      have hl : raw12854step2Labels = labelEmbedding1 ∘ raw12854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12854step2 raw12854step2Labels raw12854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw12855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12855 raw12855Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12855 raw12855Labels = mixedMoment B raw12855step0 raw12855step0Labels := by
      have hz : ∀ j, raw12855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12855step0 = (fun i j => raw12855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12855step0 raw12855; decide +kernel
      have hl : raw12855step0Labels = raw12855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12855 raw12855Labels permutation265 hz
    mixedMoment B raw12855step0 raw12855step0Labels = mixedMoment B raw12855step1 raw12855step1Labels := by
      have ha : raw12855step1 = (fun i j => raw12855step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12855step1 raw12855step0; decide +kernel
      have hl : raw12855step1Labels = raw12855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12855step0 raw12855step0Labels permutation37 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12856 raw12856Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw12856 raw12856Labels = mixedMoment B raw12856step0 raw12856step0Labels := by
      have ha : raw12856step0 = (fun i j => raw12856 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12856step0 raw12856; decide +kernel
      have hl : raw12856step0Labels = raw12856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12856 raw12856Labels permutation428 permutation4
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw12857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12857 raw12857Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw12857 raw12857Labels = mixedMoment B raw12857step0 raw12857step0Labels := by
      have hz : ∀ j, raw12857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12857step0 = (fun i j => raw12857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12857step0 raw12857; decide +kernel
      have hl : raw12857step0Labels = raw12857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12857 raw12857Labels permutation265 hz
    mixedMoment B raw12857step0 raw12857step0Labels = mixedMoment B raw12857step1 raw12857step1Labels := by
      have ha : raw12857step1 = (fun i j => raw12857step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12857step1 raw12857step0; decide +kernel
      have hl : raw12857step1Labels = raw12857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12857step0 raw12857step0Labels permutation37 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw12858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12858 raw12858Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw12858 raw12858Labels = mixedMoment B raw12858step0 raw12858step0Labels := by
      have hz : ∀ j, raw12858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12858step0 = (fun i j => raw12858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12858step0 raw12858; decide +kernel
      have hl : raw12858step0Labels = raw12858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12858 raw12858Labels permutation265 hz
    mixedMoment B raw12858step0 raw12858step0Labels = mixedMoment B raw12858step1 raw12858step1Labels := by
      have ha : raw12858step1 = (fun i j => raw12858step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12858step1 raw12858step0; decide +kernel
      have hl : raw12858step1Labels = raw12858step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12858step0 raw12858step0Labels permutation78 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw12859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12859 raw12859Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw12859 raw12859Labels = mixedMoment B raw12859step0 raw12859step0Labels := by
      have hz : ∀ j, raw12859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12859step0 = (fun i j => raw12859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12859step0 raw12859; decide +kernel
      have hl : raw12859step0Labels = raw12859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12859 raw12859Labels permutation265 hz
    mixedMoment B raw12859step0 raw12859step0Labels = mixedMoment B raw12859step1 raw12859step1Labels := by
      have ha : raw12859step1 = (fun i j => raw12859step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12859step1 raw12859step0; decide +kernel
      have hl : raw12859step1Labels = raw12859step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12859step0 raw12859step0Labels permutation75 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw12860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12860 raw12860Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw12860 raw12860Labels = mixedMoment B raw12860step0 raw12860step0Labels := by
      have hz : ∀ j, raw12860 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12860step0 = (fun i j => raw12860 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12860step0 raw12860; decide +kernel
      have hl : raw12860step0Labels = raw12860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12860 raw12860Labels permutation590 hz
    mixedMoment B raw12860step0 raw12860step0Labels = mixedMoment B raw12860step1 raw12860step1Labels := by
      have hz : ∀ j, raw12860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12860step1 = (fun i j => raw12860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12860step1 raw12860step0; decide +kernel
      have hl : raw12860step1Labels = raw12860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12860step0 raw12860step0Labels permutation56 hz
    mixedMoment B raw12860step1 raw12860step1Labels = mixedMoment B raw12860step2 raw12860step2Labels := by
      have ha : raw12860step2 = (fun i j => raw12860step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12860step2 raw12860step1; decide +kernel
      have hl : raw12860step2Labels = raw12860step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12860step1 raw12860step1Labels permutation18 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw12861 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1], ![0, 0]]
def raw12861Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw12861step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw12861step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12861step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12861step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical12861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12861 raw12861Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12861 raw12861Labels = mixedMoment B raw12861step0 raw12861step0Labels := by
      have hz : ∀ j, raw12861 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12861step0 = (fun i j => raw12861 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12861step0 raw12861; decide +kernel
      have hl : raw12861step0Labels = raw12861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861 raw12861Labels permutation590 hz
    mixedMoment B raw12861step0 raw12861step0Labels = mixedMoment B raw12861step1 raw12861step1Labels := by
      have hz : ∀ j, raw12861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12861step1 = (fun i j => raw12861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12861step1 raw12861step0; decide +kernel
      have hl : raw12861step1Labels = raw12861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12861step0 raw12861step0Labels permutation56 hz
    mixedMoment B raw12861step1 raw12861step1Labels = mixedMoment B raw12861step2 raw12861step2Labels := by
      have ha : raw12861step2 = (fun i j => raw12861step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12861step2 raw12861step1; decide +kernel
      have hl : raw12861step2Labels = raw12861step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12861step1 raw12861step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw12862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12862 raw12862Labels = mixedMoment B node1364 node1364Labels := by
  calc
    mixedMoment B raw12862 raw12862Labels = mixedMoment B raw12862step0 raw12862step0Labels := by
      have ha : raw12862step0 = (fun i j => raw12862 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12862step0 raw12862; decide +kernel
      have hl : raw12862step0Labels = raw12862Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12862 raw12862Labels permutation181 permutation2
    _ = mixedMoment B node1364 node1364Labels := by rfl

def raw12863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12863 raw12863Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw12863 raw12863Labels = mixedMoment B raw12863step0 raw12863step0Labels := by
      have hz : ∀ j, raw12863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12863step0 = (fun i j => raw12863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12863step0 raw12863; decide +kernel
      have hl : raw12863step0Labels = raw12863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12863 raw12863Labels permutation265 hz
    mixedMoment B raw12863step0 raw12863step0Labels = mixedMoment B raw12863step1 raw12863step1Labels := by
      have ha : raw12863step1 = (fun i j => raw12863step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12863step1 raw12863step0; decide +kernel
      have hl : raw12863step1Labels = raw12863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12863step0 raw12863step0Labels permutation37 permutation2
    _ = mixedMoment B node1433 node1433Labels := by rfl

def raw12864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12864 raw12864Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw12864 raw12864Labels = mixedMoment B raw12864step0 raw12864step0Labels := by
      have hz : ∀ j, raw12864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12864step0 = (fun i j => raw12864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12864step0 raw12864; decide +kernel
      have hl : raw12864step0Labels = raw12864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12864 raw12864Labels permutation265 hz
    mixedMoment B raw12864step0 raw12864step0Labels = mixedMoment B raw12864step1 raw12864step1Labels := by
      have ha : raw12864step1 = (fun i j => raw12864step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12864step1 raw12864step0; decide +kernel
      have hl : raw12864step1Labels = raw12864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12864step0 raw12864step0Labels permutation37 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw12865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12865 raw12865Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw12865 raw12865Labels = mixedMoment B raw12865step0 raw12865step0Labels := by
      have hz : ∀ j, raw12865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12865step0 = (fun i j => raw12865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12865step0 raw12865; decide +kernel
      have hl : raw12865step0Labels = raw12865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12865 raw12865Labels permutation265 hz
    mixedMoment B raw12865step0 raw12865step0Labels = mixedMoment B raw12865step1 raw12865step1Labels := by
      have ha : raw12865step1 = (fun i j => raw12865step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12865step1 raw12865step0; decide +kernel
      have hl : raw12865step1Labels = raw12865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12865step0 raw12865step0Labels permutation36 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

def raw12866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12866 raw12866Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw12866 raw12866Labels = mixedMoment B raw12866step0 raw12866step0Labels := by
      have hz : ∀ j, raw12866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12866step0 = (fun i j => raw12866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12866step0 raw12866; decide +kernel
      have hl : raw12866step0Labels = raw12866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12866 raw12866Labels permutation265 hz
    mixedMoment B raw12866step0 raw12866step0Labels = mixedMoment B raw12866step1 raw12866step1Labels := by
      have ha : raw12866step1 = (fun i j => raw12866step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12866step1 raw12866step0; decide +kernel
      have hl : raw12866step1Labels = raw12866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12866step0 raw12866step0Labels permutation34 permutation2
    _ = mixedMoment B node1371 node1371Labels := by rfl

def raw12867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12867 raw12867Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw12867 raw12867Labels = mixedMoment B raw12867step0 raw12867step0Labels := by
      have ha : raw12867step0 = (fun i j => raw12867 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12867step0 raw12867; decide +kernel
      have hl : raw12867step0Labels = raw12867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12867 raw12867Labels permutation181 permutation2
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw12868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12868 raw12868Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12868 raw12868Labels = mixedMoment B raw12868step0 raw12868step0Labels := by
      have ha : raw12868step0 = (fun i j => raw12868 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12868step0 raw12868; decide +kernel
      have hl : raw12868step0Labels = raw12868Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12868 raw12868Labels permutation183 permutation2
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw12869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12869 raw12869Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw12869 raw12869Labels = mixedMoment B raw12869step0 raw12869step0Labels := by
      have ha : raw12869step0 = (fun i j => raw12869 (permutation189 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12869step0 raw12869; decide +kernel
      have hl : raw12869step0Labels = raw12869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12869 raw12869Labels permutation189 permutation2
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw12870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12870 raw12870Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12870 raw12870Labels = mixedMoment B raw12870step0 raw12870step0Labels := by
      have hz : ∀ j, raw12870 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12870step0 = (fun i j => raw12870 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12870step0 raw12870; decide +kernel
      have hl : raw12870step0Labels = raw12870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12870 raw12870Labels permutation590 hz
    mixedMoment B raw12870step0 raw12870step0Labels = mixedMoment B raw12870step1 raw12870step1Labels := by
      have ha : raw12870step1 = (fun i j => raw12870step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12870step1 raw12870step0; decide +kernel
      have hl : raw12870step1Labels = raw12870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12870step0 raw12870step0Labels permutation39 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12871 raw12871Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw12871 raw12871Labels = mixedMoment B raw12871step0 raw12871step0Labels := by
      have ha : raw12871step0 = (fun i j => raw12871 (permutation431 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12871step0 raw12871; decide +kernel
      have hl : raw12871step0Labels = raw12871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12871 raw12871Labels permutation431 permutation4
    _ = mixedMoment B node2571 node2571Labels := by rfl

def raw12872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12872 raw12872Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw12872 raw12872Labels = mixedMoment B raw12872step0 raw12872step0Labels := by
      have ha : raw12872step0 = (fun i j => raw12872 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12872step0 raw12872; decide +kernel
      have hl : raw12872step0Labels = raw12872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12872 raw12872Labels permutation157 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw12873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12873 raw12873Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw12873 raw12873Labels = mixedMoment B raw12873step0 raw12873step0Labels := by
      have ha : raw12873step0 = (fun i j => raw12873 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12873step0 raw12873; decide +kernel
      have hl : raw12873step0Labels = raw12873Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12873 raw12873Labels permutation156 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

def raw12874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12874 raw12874Labels = mixedMoment B node2977 node2977Labels := by
  calc
    mixedMoment B raw12874 raw12874Labels = mixedMoment B raw12874step0 raw12874step0Labels := by
      have ha : raw12874step0 = (fun i j => raw12874 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12874step0 raw12874; decide +kernel
      have hl : raw12874step0Labels = raw12874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12874 raw12874Labels permutation154 permutation2
    _ = mixedMoment B node2977 node2977Labels := by rfl

def raw12875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12875 raw12875Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw12875 raw12875Labels = mixedMoment B raw12875step0 raw12875step0Labels := by
      have hz : ∀ j, raw12875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12875step0 = (fun i j => raw12875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12875step0 raw12875; decide +kernel
      have hl : raw12875step0Labels = raw12875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12875 raw12875Labels permutation265 hz
    mixedMoment B raw12875step0 raw12875step0Labels = mixedMoment B raw12875step1 raw12875step1Labels := by
      have ha : raw12875step1 = (fun i j => raw12875step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12875step1 raw12875step0; decide +kernel
      have hl : raw12875step1Labels = raw12875step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12875step0 raw12875step0Labels permutation37 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw12876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12876 raw12876Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw12876 raw12876Labels = mixedMoment B raw12876step0 raw12876step0Labels := by
      have hz : ∀ j, raw12876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12876step0 = (fun i j => raw12876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12876step0 raw12876; decide +kernel
      have hl : raw12876step0Labels = raw12876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12876 raw12876Labels permutation265 hz
    mixedMoment B raw12876step0 raw12876step0Labels = mixedMoment B raw12876step1 raw12876step1Labels := by
      have ha : raw12876step1 = (fun i j => raw12876step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12876step1 raw12876step0; decide +kernel
      have hl : raw12876step1Labels = raw12876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12876step0 raw12876step0Labels permutation36 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw12877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12877 raw12877Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw12877 raw12877Labels = mixedMoment B raw12877step0 raw12877step0Labels := by
      have hz : ∀ j, raw12877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12877step0 = (fun i j => raw12877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12877step0 raw12877; decide +kernel
      have hl : raw12877step0Labels = raw12877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12877 raw12877Labels permutation265 hz
    mixedMoment B raw12877step0 raw12877step0Labels = mixedMoment B raw12877step1 raw12877step1Labels := by
      have ha : raw12877step1 = (fun i j => raw12877step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12877step1 raw12877step0; decide +kernel
      have hl : raw12877step1Labels = raw12877step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12877step0 raw12877step0Labels permutation34 permutation2
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw12878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12878 raw12878Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw12878 raw12878Labels = mixedMoment B raw12878step0 raw12878step0Labels := by
      have hz : ∀ j, raw12878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12878step0 = (fun i j => raw12878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12878step0 raw12878; decide +kernel
      have hl : raw12878step0Labels = raw12878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12878 raw12878Labels permutation265 hz
    mixedMoment B raw12878step0 raw12878step0Labels = mixedMoment B raw12878step1 raw12878step1Labels := by
      have ha : raw12878step1 = (fun i j => raw12878step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12878step1 raw12878step0; decide +kernel
      have hl : raw12878step1Labels = raw12878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12878step0 raw12878step0Labels permutation78 permutation4
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw12879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12879 raw12879Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw12879 raw12879Labels = mixedMoment B raw12879step0 raw12879step0Labels := by
      have hz : ∀ j, raw12879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12879step0 = (fun i j => raw12879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12879step0 raw12879; decide +kernel
      have hl : raw12879step0Labels = raw12879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12879 raw12879Labels permutation265 hz
    mixedMoment B raw12879step0 raw12879step0Labels = mixedMoment B raw12879step1 raw12879step1Labels := by
      have ha : raw12879step1 = (fun i j => raw12879step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12879step1 raw12879step0; decide +kernel
      have hl : raw12879step1Labels = raw12879step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12879step0 raw12879step0Labels permutation33 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw12880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12880 raw12880Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw12880 raw12880Labels = mixedMoment B raw12880step0 raw12880step0Labels := by
      have hz : ∀ j, raw12880 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12880step0 = (fun i j => raw12880 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12880step0 raw12880; decide +kernel
      have hl : raw12880step0Labels = raw12880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12880 raw12880Labels permutation265 hz
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw12881 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12881 raw12881Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw12881 raw12881Labels = mixedMoment B raw12881step0 raw12881step0Labels := by
      have hz : ∀ j, raw12881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12881step0 = (fun i j => raw12881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12881step0 raw12881; decide +kernel
      have hl : raw12881step0Labels = raw12881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12881 raw12881Labels permutation265 hz
    mixedMoment B raw12881step0 raw12881step0Labels = mixedMoment B raw12881step1 raw12881step1Labels := by
      have ha : raw12881step1 = (fun i j => raw12881step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12881step1 raw12881step0; decide +kernel
      have hl : raw12881step1Labels = raw12881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12881step0 raw12881step0Labels permutation96 permutation3
    mixedMoment B raw12881step1 raw12881step1Labels = mixedMoment B raw12881step2 raw12881step2Labels := by
      have ha : raw12881step2 = raw12881step1 := by apply Matrix.ext; unfold raw12881step2 raw12881step1; decide +kernel
      have hl : raw12881step1Labels = labelEmbedding6 ∘ raw12881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12881step1 raw12881step1Labels raw12881step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw12882 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12882step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12882step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12882 raw12882Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw12882 raw12882Labels = mixedMoment B raw12882step0 raw12882step0Labels := by
      have hz : ∀ j, raw12882 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12882step0 = (fun i j => raw12882 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12882step0 raw12882; decide +kernel
      have hl : raw12882step0Labels = raw12882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12882 raw12882Labels permutation265 hz
    mixedMoment B raw12882step0 raw12882step0Labels = mixedMoment B raw12882step1 raw12882step1Labels := by
      have ha : raw12882step1 = (fun i j => raw12882step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12882step1 raw12882step0; decide +kernel
      have hl : raw12882step1Labels = raw12882step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12882step0 raw12882step0Labels permutation36 permutation7
    mixedMoment B raw12882step1 raw12882step1Labels = mixedMoment B raw12882step2 raw12882step2Labels := by
      have ha : raw12882step2 = raw12882step1 := by apply Matrix.ext; unfold raw12882step2 raw12882step1; decide +kernel
      have hl : raw12882step1Labels = labelEmbedding10 ∘ raw12882step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12882step1 raw12882step1Labels raw12882step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw12883 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12883step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12883 raw12883Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw12883 raw12883Labels = mixedMoment B raw12883step0 raw12883step0Labels := by
      have hz : ∀ j, raw12883 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12883step0 = (fun i j => raw12883 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12883step0 raw12883; decide +kernel
      have hl : raw12883step0Labels = raw12883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12883 raw12883Labels permutation265 hz
    mixedMoment B raw12883step0 raw12883step0Labels = mixedMoment B raw12883step1 raw12883step1Labels := by
      have ha : raw12883step1 = (fun i j => raw12883step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12883step1 raw12883step0; decide +kernel
      have hl : raw12883step1Labels = raw12883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12883step0 raw12883step0Labels permutation35 permutation7
    mixedMoment B raw12883step1 raw12883step1Labels = mixedMoment B raw12883step2 raw12883step2Labels := by
      have ha : raw12883step2 = raw12883step1 := by apply Matrix.ext; unfold raw12883step2 raw12883step1; decide +kernel
      have hl : raw12883step1Labels = labelEmbedding10 ∘ raw12883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12883step1 raw12883step1Labels raw12883step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw12884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw12884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12884 raw12884Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw12884 raw12884Labels = mixedMoment B raw12884step0 raw12884step0Labels := by
      have ha : raw12884step0 = (fun i j => raw12884 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12884step0 raw12884; decide +kernel
      have hl : raw12884step0Labels = raw12884Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12884 raw12884Labels permutation213 permutation4
    mixedMoment B raw12884step0 raw12884step0Labels = mixedMoment B raw12884step1 raw12884step1Labels := by
      have ha : raw12884step1 = -raw12884step0 := by apply Matrix.ext; change ∀ i j, raw12884step1 i j = -(raw12884step0 i j); unfold raw12884step1 raw12884step0; decide +kernel
      have hl : raw12884step1Labels = raw12884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12884step1 raw12884step1Labels = mixedMoment B raw12884step2 raw12884step2Labels := by
      have ha : raw12884step2 = raw12884step1 := by apply Matrix.ext; unfold raw12884step2 raw12884step1; decide +kernel
      have hl : raw12884step1Labels = labelEmbedding7 ∘ raw12884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12884step1 raw12884step1Labels raw12884step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw12885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12885step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12885 raw12885Labels = mixedMoment B node5143 node5143Labels := by
  calc
    mixedMoment B raw12885 raw12885Labels = mixedMoment B raw12885step0 raw12885step0Labels := by
      have ha : raw12885step0 = (fun i j => raw12885 (permutation499 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12885step0 raw12885; decide +kernel
      have hl : raw12885step0Labels = raw12885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12885 raw12885Labels permutation499 permutation3
    mixedMoment B raw12885step0 raw12885step0Labels = mixedMoment B raw12885step1 raw12885step1Labels := by
      have ha : raw12885step1 = raw12885step0 := by apply Matrix.ext; unfold raw12885step1 raw12885step0; decide +kernel
      have hl : raw12885step0Labels = labelEmbedding6 ∘ raw12885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12885step0 raw12885step0Labels raw12885step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5143 node5143Labels := by rfl

def raw12886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12886step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12886 raw12886Labels = mixedMoment B node5285 node5285Labels := by
  calc
    mixedMoment B raw12886 raw12886Labels = mixedMoment B raw12886step0 raw12886step0Labels := by
      have ha : raw12886step0 = (fun i j => raw12886 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12886step0 raw12886; decide +kernel
      have hl : raw12886step0Labels = raw12886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12886 raw12886Labels permutation152 permutation6
    mixedMoment B raw12886step0 raw12886step0Labels = mixedMoment B raw12886step1 raw12886step1Labels := by
      have ha : raw12886step1 = raw12886step0 := by apply Matrix.ext; unfold raw12886step1 raw12886step0; decide +kernel
      have hl : raw12886step0Labels = labelEmbedding9 ∘ raw12886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12886step0 raw12886step0Labels raw12886step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5285 node5285Labels := by rfl

def raw12887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12887step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12887 raw12887Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw12887 raw12887Labels = mixedMoment B raw12887step0 raw12887step0Labels := by
      have ha : raw12887step0 = (fun i j => raw12887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12887step0 raw12887; decide +kernel
      have hl : raw12887step0Labels = raw12887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12887 raw12887Labels permutation152 permutation6
    mixedMoment B raw12887step0 raw12887step0Labels = mixedMoment B raw12887step1 raw12887step1Labels := by
      have ha : raw12887step1 = raw12887step0 := by apply Matrix.ext; unfold raw12887step1 raw12887step0; decide +kernel
      have hl : raw12887step0Labels = labelEmbedding9 ∘ raw12887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12887step0 raw12887step0Labels raw12887step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw12888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12888step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12888 raw12888Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw12888 raw12888Labels = mixedMoment B raw12888step0 raw12888step0Labels := by
      have hz : ∀ j, raw12888 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12888step0 = (fun i j => raw12888 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12888step0 raw12888; decide +kernel
      have hl : raw12888step0Labels = raw12888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12888 raw12888Labels permutation265 hz
    mixedMoment B raw12888step0 raw12888step0Labels = mixedMoment B raw12888step1 raw12888step1Labels := by
      have ha : raw12888step1 = (fun i j => raw12888step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12888step1 raw12888step0; decide +kernel
      have hl : raw12888step1Labels = raw12888step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12888step0 raw12888step0Labels permutation79 permutation5
    mixedMoment B raw12888step1 raw12888step1Labels = mixedMoment B raw12888step2 raw12888step2Labels := by
      have ha : raw12888step2 = raw12888step1 := by apply Matrix.ext; unfold raw12888step2 raw12888step1; decide +kernel
      have hl : raw12888step1Labels = labelEmbedding8 ∘ raw12888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12888step1 raw12888step1Labels raw12888step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw12889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12889step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12889 raw12889Labels = mixedMoment B node4809 node4809Labels := by
  calc
    mixedMoment B raw12889 raw12889Labels = mixedMoment B raw12889step0 raw12889step0Labels := by
      have hz : ∀ j, raw12889 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12889step0 = (fun i j => raw12889 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12889step0 raw12889; decide +kernel
      have hl : raw12889step0Labels = raw12889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12889 raw12889Labels permutation265 hz
    mixedMoment B raw12889step0 raw12889step0Labels = mixedMoment B raw12889step1 raw12889step1Labels := by
      have ha : raw12889step1 = (fun i j => raw12889step0 (permutation78 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12889step1 raw12889step0; decide +kernel
      have hl : raw12889step1Labels = raw12889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12889step0 raw12889step0Labels permutation78 permutation5
    mixedMoment B raw12889step1 raw12889step1Labels = mixedMoment B raw12889step2 raw12889step2Labels := by
      have ha : raw12889step2 = raw12889step1 := by apply Matrix.ext; unfold raw12889step2 raw12889step1; decide +kernel
      have hl : raw12889step1Labels = labelEmbedding8 ∘ raw12889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12889step1 raw12889step1Labels raw12889step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4809 node4809Labels := by rfl

def raw12890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12890step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12890 raw12890Labels = mixedMoment B node4842 node4842Labels := by
  calc
    mixedMoment B raw12890 raw12890Labels = mixedMoment B raw12890step0 raw12890step0Labels := by
      have hz : ∀ j, raw12890 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12890step0 = (fun i j => raw12890 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12890step0 raw12890; decide +kernel
      have hl : raw12890step0Labels = raw12890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12890 raw12890Labels permutation265 hz
    mixedMoment B raw12890step0 raw12890step0Labels = mixedMoment B raw12890step1 raw12890step1Labels := by
      have ha : raw12890step1 = (fun i j => raw12890step0 (permutation77 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12890step1 raw12890step0; decide +kernel
      have hl : raw12890step1Labels = raw12890step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12890step0 raw12890step0Labels permutation77 permutation5
    mixedMoment B raw12890step1 raw12890step1Labels = mixedMoment B raw12890step2 raw12890step2Labels := by
      have ha : raw12890step2 = raw12890step1 := by apply Matrix.ext; unfold raw12890step2 raw12890step1; decide +kernel
      have hl : raw12890step1Labels = labelEmbedding8 ∘ raw12890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12890step1 raw12890step1Labels raw12890step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4842 node4842Labels := by rfl

def raw12891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12891step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12891 raw12891Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw12891 raw12891Labels = mixedMoment B raw12891step0 raw12891step0Labels := by
      have hz : ∀ j, raw12891 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12891step0 = (fun i j => raw12891 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12891step0 raw12891; decide +kernel
      have hl : raw12891step0Labels = raw12891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12891 raw12891Labels permutation265 hz
    mixedMoment B raw12891step0 raw12891step0Labels = mixedMoment B raw12891step1 raw12891step1Labels := by
      have ha : raw12891step1 = (fun i j => raw12891step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12891step1 raw12891step0; decide +kernel
      have hl : raw12891step1Labels = raw12891step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12891step0 raw12891step0Labels permutation59 permutation3
    mixedMoment B raw12891step1 raw12891step1Labels = mixedMoment B raw12891step2 raw12891step2Labels := by
      have ha : raw12891step2 = -raw12891step1 := by apply Matrix.ext; change ∀ i j, raw12891step2 i j = -(raw12891step1 i j); unfold raw12891step2 raw12891step1; decide +kernel
      have hl : raw12891step2Labels = raw12891step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12891step2 raw12891step2Labels = mixedMoment B raw12891step3 raw12891step3Labels := by
      have ha : raw12891step3 = raw12891step2 := by apply Matrix.ext; unfold raw12891step3 raw12891step2; decide +kernel
      have hl : raw12891step2Labels = labelEmbedding6 ∘ raw12891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12891step2 raw12891step2Labels raw12891step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw12892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12892step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12892step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12892 raw12892Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw12892 raw12892Labels = mixedMoment B raw12892step0 raw12892step0Labels := by
      have hz : ∀ j, raw12892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12892step0 = (fun i j => raw12892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12892step0 raw12892; decide +kernel
      have hl : raw12892step0Labels = raw12892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12892 raw12892Labels permutation265 hz
    mixedMoment B raw12892step0 raw12892step0Labels = mixedMoment B raw12892step1 raw12892step1Labels := by
      have ha : raw12892step1 = (fun i j => raw12892step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12892step1 raw12892step0; decide +kernel
      have hl : raw12892step1Labels = raw12892step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12892step0 raw12892step0Labels permutation41 permutation4
    mixedMoment B raw12892step1 raw12892step1Labels = mixedMoment B raw12892step2 raw12892step2Labels := by
      have ha : raw12892step2 = -raw12892step1 := by apply Matrix.ext; change ∀ i j, raw12892step2 i j = -(raw12892step1 i j); unfold raw12892step2 raw12892step1; decide +kernel
      have hl : raw12892step2Labels = raw12892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12892step2 raw12892step2Labels = mixedMoment B raw12892step3 raw12892step3Labels := by
      have ha : raw12892step3 = raw12892step2 := by apply Matrix.ext; unfold raw12892step3 raw12892step2; decide +kernel
      have hl : raw12892step2Labels = labelEmbedding7 ∘ raw12892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12892step2 raw12892step2Labels raw12892step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw12893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw12893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw12893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12893 raw12893Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw12893 raw12893Labels = mixedMoment B raw12893step0 raw12893step0Labels := by
      have hz : ∀ j, raw12893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12893step0 = (fun i j => raw12893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12893step0 raw12893; decide +kernel
      have hl : raw12893step0Labels = raw12893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12893 raw12893Labels permutation265 hz
    mixedMoment B raw12893step0 raw12893step0Labels = mixedMoment B raw12893step1 raw12893step1Labels := by
      have ha : raw12893step1 = (fun i j => raw12893step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12893step1 raw12893step0; decide +kernel
      have hl : raw12893step1Labels = raw12893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12893step0 raw12893step0Labels permutation96 permutation3
    mixedMoment B raw12893step1 raw12893step1Labels = mixedMoment B raw12893step2 raw12893step2Labels := by
      have ha : raw12893step2 = raw12893step1 := by apply Matrix.ext; unfold raw12893step2 raw12893step1; decide +kernel
      have hl : raw12893step1Labels = labelEmbedding6 ∘ raw12893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12893step1 raw12893step1Labels raw12893step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw12894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12894step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12894 raw12894Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12894 raw12894Labels = mixedMoment B raw12894step0 raw12894step0Labels := by
      have hz : ∀ j, raw12894 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12894step0 = (fun i j => raw12894 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12894step0 raw12894; decide +kernel
      have hl : raw12894step0Labels = raw12894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12894 raw12894Labels permutation265 hz
    mixedMoment B raw12894step0 raw12894step0Labels = mixedMoment B raw12894step1 raw12894step1Labels := by
      have ha : raw12894step1 = (fun i j => raw12894step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12894step1 raw12894step0; decide +kernel
      have hl : raw12894step1Labels = raw12894step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12894step0 raw12894step0Labels permutation33 permutation6
    mixedMoment B raw12894step1 raw12894step1Labels = mixedMoment B raw12894step2 raw12894step2Labels := by
      have ha : raw12894step2 = raw12894step1 := by apply Matrix.ext; unfold raw12894step2 raw12894step1; decide +kernel
      have hl : raw12894step1Labels = labelEmbedding9 ∘ raw12894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12894step1 raw12894step1Labels raw12894step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12895 raw12895Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw12895 raw12895Labels = mixedMoment B raw12895step0 raw12895step0Labels := by
      have hz : ∀ j, raw12895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12895step0 = (fun i j => raw12895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12895step0 raw12895; decide +kernel
      have hl : raw12895step0Labels = raw12895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12895 raw12895Labels permutation265 hz
    mixedMoment B raw12895step0 raw12895step0Labels = mixedMoment B raw12895step1 raw12895step1Labels := by
      have ha : raw12895step1 = (fun i j => raw12895step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12895step1 raw12895step0; decide +kernel
      have hl : raw12895step1Labels = raw12895step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12895step0 raw12895step0Labels permutation96 permutation3
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw12896 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12896 raw12896Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw12896 raw12896Labels = mixedMoment B raw12896step0 raw12896step0Labels := by
      have hz : ∀ j, raw12896 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12896step0 = (fun i j => raw12896 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12896step0 raw12896; decide +kernel
      have hl : raw12896step0Labels = raw12896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12896 raw12896Labels permutation265 hz
    mixedMoment B raw12896step0 raw12896step0Labels = mixedMoment B raw12896step1 raw12896step1Labels := by
      have ha : raw12896step1 = (fun i j => raw12896step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12896step1 raw12896step0; decide +kernel
      have hl : raw12896step1Labels = raw12896step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12896step0 raw12896step0Labels permutation32 permutation6
    _ = mixedMoment B node3115 node3115Labels := by rfl

def raw12897 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12897 raw12897Labels = mixedMoment B node3116 node3116Labels := by
  calc
    mixedMoment B raw12897 raw12897Labels = mixedMoment B raw12897step0 raw12897step0Labels := by
      have hz : ∀ j, raw12897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12897step0 = (fun i j => raw12897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12897step0 raw12897; decide +kernel
      have hl : raw12897step0Labels = raw12897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12897 raw12897Labels permutation265 hz
    mixedMoment B raw12897step0 raw12897step0Labels = mixedMoment B raw12897step1 raw12897step1Labels := by
      have ha : raw12897step1 = (fun i j => raw12897step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12897step1 raw12897step0; decide +kernel
      have hl : raw12897step1Labels = raw12897step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12897step0 raw12897step0Labels permutation32 permutation6
    _ = mixedMoment B node3116 node3116Labels := by rfl

def raw12898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12898 raw12898Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw12898 raw12898Labels = mixedMoment B raw12898step0 raw12898step0Labels := by
      have ha : raw12898step0 = (fun i j => raw12898 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12898step0 raw12898; decide +kernel
      have hl : raw12898step0Labels = raw12898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12898 raw12898Labels permutation152 permutation6
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw12899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw12899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12899 raw12899Labels = mixedMoment B node2565 node2565Labels := by
  calc
    mixedMoment B raw12899 raw12899Labels = mixedMoment B raw12899step0 raw12899step0Labels := by
      have ha : raw12899step0 = (fun i j => raw12899 (permutation499 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12899step0 raw12899; decide +kernel
      have hl : raw12899step0Labels = raw12899Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12899 raw12899Labels permutation499 permutation3
    _ = mixedMoment B node2565 node2565Labels := by rfl

def raw12900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw12900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12900 raw12900Labels = mixedMoment B node2756 node2756Labels := by
  calc
    mixedMoment B raw12900 raw12900Labels = mixedMoment B raw12900step0 raw12900step0Labels := by
      have ha : raw12900step0 = (fun i j => raw12900 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12900step0 raw12900; decide +kernel
      have hl : raw12900step0Labels = raw12900Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12900 raw12900Labels permutation152 permutation6
    _ = mixedMoment B node2756 node2756Labels := by rfl

def raw12901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12901 raw12901Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw12901 raw12901Labels = mixedMoment B raw12901step0 raw12901step0Labels := by
      have ha : raw12901step0 = (fun i j => raw12901 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12901step0 raw12901; decide +kernel
      have hl : raw12901step0Labels = raw12901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12901 raw12901Labels permutation152 permutation6
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw12902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw12902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw12902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12902 raw12902Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw12902 raw12902Labels = mixedMoment B raw12902step0 raw12902step0Labels := by
      have hz : ∀ j, raw12902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12902step0 = (fun i j => raw12902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12902step0 raw12902; decide +kernel
      have hl : raw12902step0Labels = raw12902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12902 raw12902Labels permutation265 hz
    mixedMoment B raw12902step0 raw12902step0Labels = mixedMoment B raw12902step1 raw12902step1Labels := by
      have ha : raw12902step1 = (fun i j => raw12902step0 (permutation75 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12902step1 raw12902step0; decide +kernel
      have hl : raw12902step1Labels = raw12902step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12902step0 raw12902step0Labels permutation75 permutation3
    mixedMoment B raw12902step1 raw12902step1Labels = mixedMoment B raw12902step2 raw12902step2Labels := by
      have ha : raw12902step2 = -raw12902step1 := by apply Matrix.ext; change ∀ i j, raw12902step2 i j = -(raw12902step1 i j); unfold raw12902step2 raw12902step1; decide +kernel
      have hl : raw12902step2Labels = raw12902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw12903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12903step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw12903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw12903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12903 raw12903Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw12903 raw12903Labels = mixedMoment B raw12903step0 raw12903step0Labels := by
      have hz : ∀ j, raw12903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12903step0 = (fun i j => raw12903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12903step0 raw12903; decide +kernel
      have hl : raw12903step0Labels = raw12903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12903 raw12903Labels permutation265 hz
    mixedMoment B raw12903step0 raw12903step0Labels = mixedMoment B raw12903step1 raw12903step1Labels := by
      have ha : raw12903step1 = (fun i j => raw12903step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12903step1 raw12903step0; decide +kernel
      have hl : raw12903step1Labels = raw12903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12903step0 raw12903step0Labels permutation61 permutation3
    mixedMoment B raw12903step1 raw12903step1Labels = mixedMoment B raw12903step2 raw12903step2Labels := by
      have ha : raw12903step2 = -raw12903step1 := by apply Matrix.ext; change ∀ i j, raw12903step2 i j = -(raw12903step1 i j); unfold raw12903step2 raw12903step1; decide +kernel
      have hl : raw12903step2Labels = raw12903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

def raw12904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw12904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12904 raw12904Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw12904 raw12904Labels = mixedMoment B raw12904step0 raw12904step0Labels := by
      have hz : ∀ j, raw12904 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12904step0 = (fun i j => raw12904 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12904step0 raw12904; decide +kernel
      have hl : raw12904step0Labels = raw12904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12904 raw12904Labels permutation265 hz
    mixedMoment B raw12904step0 raw12904step0Labels = mixedMoment B raw12904step1 raw12904step1Labels := by
      have ha : raw12904step1 = (fun i j => raw12904step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12904step1 raw12904step0; decide +kernel
      have hl : raw12904step1Labels = raw12904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12904step0 raw12904step0Labels permutation60 permutation3
    mixedMoment B raw12904step1 raw12904step1Labels = mixedMoment B raw12904step2 raw12904step2Labels := by
      have ha : raw12904step2 = -raw12904step1 := by apply Matrix.ext; change ∀ i j, raw12904step2 i j = -(raw12904step1 i j); unfold raw12904step2 raw12904step1; decide +kernel
      have hl : raw12904step2Labels = raw12904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2123 node2123Labels := by rfl

def raw12905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12905 raw12905Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw12905 raw12905Labels = mixedMoment B raw12905step0 raw12905step0Labels := by
      have hz : ∀ j, raw12905 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12905step0 = (fun i j => raw12905 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12905step0 raw12905; decide +kernel
      have hl : raw12905step0Labels = raw12905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12905 raw12905Labels permutation265 hz
    mixedMoment B raw12905step0 raw12905step0Labels = mixedMoment B raw12905step1 raw12905step1Labels := by
      have ha : raw12905step1 = (fun i j => raw12905step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12905step1 raw12905step0; decide +kernel
      have hl : raw12905step1Labels = raw12905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12905step0 raw12905step0Labels permutation59 permutation3
    mixedMoment B raw12905step1 raw12905step1Labels = mixedMoment B raw12905step2 raw12905step2Labels := by
      have ha : raw12905step2 = -raw12905step1 := by apply Matrix.ext; change ∀ i j, raw12905step2 i j = -(raw12905step1 i j); unfold raw12905step2 raw12905step1; decide +kernel
      have hl : raw12905step2Labels = raw12905step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw12906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12906 raw12906Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw12906 raw12906Labels = mixedMoment B raw12906step0 raw12906step0Labels := by
      have hz : ∀ j, raw12906 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12906step0 = (fun i j => raw12906 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12906step0 raw12906; decide +kernel
      have hl : raw12906step0Labels = raw12906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12906 raw12906Labels permutation265 hz
    mixedMoment B raw12906step0 raw12906step0Labels = mixedMoment B raw12906step1 raw12906step1Labels := by
      have ha : raw12906step1 = (fun i j => raw12906step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12906step1 raw12906step0; decide +kernel
      have hl : raw12906step1Labels = raw12906step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12906step0 raw12906step0Labels permutation32 permutation6
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw12907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw12907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12907 raw12907Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw12907 raw12907Labels = mixedMoment B raw12907step0 raw12907step0Labels := by
      have hz : ∀ j, raw12907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12907step0 = (fun i j => raw12907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12907step0 raw12907; decide +kernel
      have hl : raw12907step0Labels = raw12907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12907 raw12907Labels permutation265 hz
    mixedMoment B raw12907step0 raw12907step0Labels = mixedMoment B raw12907step1 raw12907step1Labels := by
      have ha : raw12907step1 = (fun i j => raw12907step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12907step1 raw12907step0; decide +kernel
      have hl : raw12907step1Labels = raw12907step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12907step0 raw12907step0Labels permutation96 permutation3
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw12908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12908 raw12908Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12908 raw12908Labels = mixedMoment B raw12908step0 raw12908step0Labels := by
      have hz : ∀ j, raw12908 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12908step0 = (fun i j => raw12908 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12908step0 raw12908; decide +kernel
      have hl : raw12908step0Labels = raw12908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12908 raw12908Labels permutation265 hz
    mixedMoment B raw12908step0 raw12908step0Labels = mixedMoment B raw12908step1 raw12908step1Labels := by
      have ha : raw12908step1 = (fun i j => raw12908step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12908step1 raw12908step0; decide +kernel
      have hl : raw12908step1Labels = raw12908step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12908step0 raw12908step0Labels permutation33 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12909 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12909step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12909step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12909 raw12909Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw12909 raw12909Labels = mixedMoment B raw12909step0 raw12909step0Labels := by
      have hz : ∀ j, raw12909 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12909step0 = (fun i j => raw12909 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12909step0 raw12909; decide +kernel
      have hl : raw12909step0Labels = raw12909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12909 raw12909Labels permutation265 hz
    mixedMoment B raw12909step0 raw12909step0Labels = mixedMoment B raw12909step1 raw12909step1Labels := by
      have ha : raw12909step1 = (fun i j => raw12909step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12909step1 raw12909step0; decide +kernel
      have hl : raw12909step1Labels = raw12909step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12909step0 raw12909step0Labels permutation37 permutation7
    mixedMoment B raw12909step1 raw12909step1Labels = mixedMoment B raw12909step2 raw12909step2Labels := by
      have ha : raw12909step2 = raw12909step1 := by apply Matrix.ext; unfold raw12909step2 raw12909step1; decide +kernel
      have hl : raw12909step1Labels = labelEmbedding1 ∘ raw12909step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12909step1 raw12909step1Labels raw12909step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw12910 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12910Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12910step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12910 raw12910Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw12910 raw12910Labels = mixedMoment B raw12910step0 raw12910step0Labels := by
      have hz : ∀ j, raw12910 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12910step0 = (fun i j => raw12910 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12910step0 raw12910; decide +kernel
      have hl : raw12910step0Labels = raw12910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12910 raw12910Labels permutation265 hz
    mixedMoment B raw12910step0 raw12910step0Labels = mixedMoment B raw12910step1 raw12910step1Labels := by
      have ha : raw12910step1 = (fun i j => raw12910step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12910step1 raw12910step0; decide +kernel
      have hl : raw12910step1Labels = raw12910step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12910step0 raw12910step0Labels permutation36 permutation7
    mixedMoment B raw12910step1 raw12910step1Labels = mixedMoment B raw12910step2 raw12910step2Labels := by
      have ha : raw12910step2 = raw12910step1 := by apply Matrix.ext; unfold raw12910step2 raw12910step1; decide +kernel
      have hl : raw12910step1Labels = labelEmbedding1 ∘ raw12910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12910step1 raw12910step1Labels raw12910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw12911 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12911Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12911step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12911 raw12911Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw12911 raw12911Labels = mixedMoment B raw12911step0 raw12911step0Labels := by
      have hz : ∀ j, raw12911 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12911step0 = (fun i j => raw12911 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12911step0 raw12911; decide +kernel
      have hl : raw12911step0Labels = raw12911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12911 raw12911Labels permutation265 hz
    mixedMoment B raw12911step0 raw12911step0Labels = mixedMoment B raw12911step1 raw12911step1Labels := by
      have ha : raw12911step1 = (fun i j => raw12911step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12911step1 raw12911step0; decide +kernel
      have hl : raw12911step1Labels = raw12911step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12911step0 raw12911step0Labels permutation35 permutation7
    mixedMoment B raw12911step1 raw12911step1Labels = mixedMoment B raw12911step2 raw12911step2Labels := by
      have ha : raw12911step2 = raw12911step1 := by apply Matrix.ext; unfold raw12911step2 raw12911step1; decide +kernel
      have hl : raw12911step1Labels = labelEmbedding1 ∘ raw12911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12911step1 raw12911step1Labels raw12911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw12912 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12912Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw12912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12912step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12912 raw12912Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw12912 raw12912Labels = mixedMoment B raw12912step0 raw12912step0Labels := by
      have ha : raw12912step0 = (fun i j => raw12912 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12912step0 raw12912; decide +kernel
      have hl : raw12912step0Labels = raw12912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12912 raw12912Labels permutation216 permutation5
    mixedMoment B raw12912step0 raw12912step0Labels = mixedMoment B raw12912step1 raw12912step1Labels := by
      have ha : raw12912step1 = -raw12912step0 := by apply Matrix.ext; change ∀ i j, raw12912step1 i j = -(raw12912step0 i j); unfold raw12912step1 raw12912step0; decide +kernel
      have hl : raw12912step1Labels = raw12912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12912step1 raw12912step1Labels = mixedMoment B raw12912step2 raw12912step2Labels := by
      have ha : raw12912step2 = raw12912step1 := by apply Matrix.ext; unfold raw12912step2 raw12912step1; decide +kernel
      have hl : raw12912step1Labels = labelEmbedding1 ∘ raw12912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12912step1 raw12912step1Labels raw12912step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3170 node3170Labels := by rfl

def raw12913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12913Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12913 raw12913Labels = mixedMoment B node3020 node3020Labels := by
  calc
    mixedMoment B raw12913 raw12913Labels = mixedMoment B raw12913step0 raw12913step0Labels := by
      have ha : raw12913step0 = (fun i j => raw12913 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12913step0 raw12913; decide +kernel
      have hl : raw12913step0Labels = raw12913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12913 raw12913Labels permutation181 permutation7
    mixedMoment B raw12913step0 raw12913step0Labels = mixedMoment B raw12913step1 raw12913step1Labels := by
      have ha : raw12913step1 = raw12913step0 := by apply Matrix.ext; unfold raw12913step1 raw12913step0; decide +kernel
      have hl : raw12913step0Labels = labelEmbedding1 ∘ raw12913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12913step0 raw12913step0Labels raw12913step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3020 node3020Labels := by rfl

def raw12914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12914Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12914 raw12914Labels = mixedMoment B node3021 node3021Labels := by
  calc
    mixedMoment B raw12914 raw12914Labels = mixedMoment B raw12914step0 raw12914step0Labels := by
      have ha : raw12914step0 = (fun i j => raw12914 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12914step0 raw12914; decide +kernel
      have hl : raw12914step0Labels = raw12914Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12914 raw12914Labels permutation180 permutation7
    mixedMoment B raw12914step0 raw12914step0Labels = mixedMoment B raw12914step1 raw12914step1Labels := by
      have ha : raw12914step1 = raw12914step0 := by apply Matrix.ext; unfold raw12914step1 raw12914step0; decide +kernel
      have hl : raw12914step0Labels = labelEmbedding1 ∘ raw12914step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12914step0 raw12914step0Labels raw12914step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3021 node3021Labels := by rfl

def raw12915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12915Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12915step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12915 raw12915Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw12915 raw12915Labels = mixedMoment B raw12915step0 raw12915step0Labels := by
      have ha : raw12915step0 = (fun i j => raw12915 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12915step0 raw12915; decide +kernel
      have hl : raw12915step0Labels = raw12915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12915 raw12915Labels permutation179 permutation7
    mixedMoment B raw12915step0 raw12915step0Labels = mixedMoment B raw12915step1 raw12915step1Labels := by
      have ha : raw12915step1 = raw12915step0 := by apply Matrix.ext; unfold raw12915step1 raw12915step0; decide +kernel
      have hl : raw12915step0Labels = labelEmbedding1 ∘ raw12915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12915step0 raw12915step0Labels raw12915step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw12916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12916Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12916step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw12916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12916 raw12916Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw12916 raw12916Labels = mixedMoment B raw12916step0 raw12916step0Labels := by
      have hz : ∀ j, raw12916 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12916step0 = (fun i j => raw12916 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12916step0 raw12916; decide +kernel
      have hl : raw12916step0Labels = raw12916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12916 raw12916Labels permutation265 hz
    mixedMoment B raw12916step0 raw12916step0Labels = mixedMoment B raw12916step1 raw12916step1Labels := by
      have ha : raw12916step1 = (fun i j => raw12916step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12916step1 raw12916step0; decide +kernel
      have hl : raw12916step1Labels = raw12916step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12916step0 raw12916step0Labels permutation79 permutation5
    mixedMoment B raw12916step1 raw12916step1Labels = mixedMoment B raw12916step2 raw12916step2Labels := by
      have ha : raw12916step2 = raw12916step1 := by apply Matrix.ext; unfold raw12916step2 raw12916step1; decide +kernel
      have hl : raw12916step1Labels = labelEmbedding1 ∘ raw12916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12916step1 raw12916step1Labels raw12916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw12917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12917step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12917step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw12917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12917 raw12917Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw12917 raw12917Labels = mixedMoment B raw12917step0 raw12917step0Labels := by
      have hz : ∀ j, raw12917 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12917step0 = (fun i j => raw12917 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12917step0 raw12917; decide +kernel
      have hl : raw12917step0Labels = raw12917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12917 raw12917Labels permutation265 hz
    mixedMoment B raw12917step0 raw12917step0Labels = mixedMoment B raw12917step1 raw12917step1Labels := by
      have ha : raw12917step1 = (fun i j => raw12917step0 (permutation78 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12917step1 raw12917step0; decide +kernel
      have hl : raw12917step1Labels = raw12917step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12917step0 raw12917step0Labels permutation78 permutation5
    mixedMoment B raw12917step1 raw12917step1Labels = mixedMoment B raw12917step2 raw12917step2Labels := by
      have ha : raw12917step2 = raw12917step1 := by apply Matrix.ext; unfold raw12917step2 raw12917step1; decide +kernel
      have hl : raw12917step1Labels = labelEmbedding1 ∘ raw12917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12917step1 raw12917step1Labels raw12917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2027 node2027Labels := by rfl

def raw12918 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw12918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12918 raw12918Labels = mixedMoment B node2061 node2061Labels := by
  calc
    mixedMoment B raw12918 raw12918Labels = mixedMoment B raw12918step0 raw12918step0Labels := by
      have hz : ∀ j, raw12918 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12918step0 = (fun i j => raw12918 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12918step0 raw12918; decide +kernel
      have hl : raw12918step0Labels = raw12918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12918 raw12918Labels permutation265 hz
    mixedMoment B raw12918step0 raw12918step0Labels = mixedMoment B raw12918step1 raw12918step1Labels := by
      have ha : raw12918step1 = (fun i j => raw12918step0 (permutation77 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12918step1 raw12918step0; decide +kernel
      have hl : raw12918step1Labels = raw12918step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12918step0 raw12918step0Labels permutation77 permutation5
    mixedMoment B raw12918step1 raw12918step1Labels = mixedMoment B raw12918step2 raw12918step2Labels := by
      have ha : raw12918step2 = raw12918step1 := by apply Matrix.ext; unfold raw12918step2 raw12918step1; decide +kernel
      have hl : raw12918step1Labels = labelEmbedding1 ∘ raw12918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12918step1 raw12918step1Labels raw12918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2061 node2061Labels := by rfl

def raw12919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12919 raw12919Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw12919 raw12919Labels = mixedMoment B raw12919step0 raw12919step0Labels := by
      have hz : ∀ j, raw12919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12919step0 = (fun i j => raw12919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12919step0 raw12919; decide +kernel
      have hl : raw12919step0Labels = raw12919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12919 raw12919Labels permutation265 hz
    mixedMoment B raw12919step0 raw12919step0Labels = mixedMoment B raw12919step1 raw12919step1Labels := by
      have ha : raw12919step1 = (fun i j => raw12919step0 (permutation73 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12919step1 raw12919step0; decide +kernel
      have hl : raw12919step1Labels = raw12919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12919step0 raw12919step0Labels permutation73 permutation5
    mixedMoment B raw12919step1 raw12919step1Labels = mixedMoment B raw12919step2 raw12919step2Labels := by
      have ha : raw12919step2 = raw12919step1 := by apply Matrix.ext; unfold raw12919step2 raw12919step1; decide +kernel
      have hl : raw12919step1Labels = labelEmbedding1 ∘ raw12919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12919step1 raw12919step1Labels raw12919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw12920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12920step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12920step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12920step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12920step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12920 raw12920Labels = mixedMoment B node3183 node3183Labels := by
  calc
    mixedMoment B raw12920 raw12920Labels = mixedMoment B raw12920step0 raw12920step0Labels := by
      have hz : ∀ j, raw12920 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12920step0 = (fun i j => raw12920 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12920step0 raw12920; decide +kernel
      have hl : raw12920step0Labels = raw12920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12920 raw12920Labels permutation265 hz
    mixedMoment B raw12920step0 raw12920step0Labels = mixedMoment B raw12920step1 raw12920step1Labels := by
      have ha : raw12920step1 = (fun i j => raw12920step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12920step1 raw12920step0; decide +kernel
      have hl : raw12920step1Labels = raw12920step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12920step0 raw12920step0Labels permutation41 permutation5
    mixedMoment B raw12920step1 raw12920step1Labels = mixedMoment B raw12920step2 raw12920step2Labels := by
      have ha : raw12920step2 = -raw12920step1 := by apply Matrix.ext; change ∀ i j, raw12920step2 i j = -(raw12920step1 i j); unfold raw12920step2 raw12920step1; decide +kernel
      have hl : raw12920step2Labels = raw12920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12920step2 raw12920step2Labels = mixedMoment B raw12920step3 raw12920step3Labels := by
      have ha : raw12920step3 = raw12920step2 := by apply Matrix.ext; unfold raw12920step3 raw12920step2; decide +kernel
      have hl : raw12920step2Labels = labelEmbedding1 ∘ raw12920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12920step2 raw12920step2Labels raw12920step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3183 node3183Labels := by rfl

def raw12921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-3, 2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12921step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12921 raw12921Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw12921 raw12921Labels = mixedMoment B raw12921step0 raw12921step0Labels := by
      have hz : ∀ j, raw12921 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12921step0 = (fun i j => raw12921 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12921step0 raw12921; decide +kernel
      have hl : raw12921step0Labels = raw12921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12921 raw12921Labels permutation265 hz
    mixedMoment B raw12921step0 raw12921step0Labels = mixedMoment B raw12921step1 raw12921step1Labels := by
      have ha : raw12921step1 = (fun i j => raw12921step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12921step1 raw12921step0; decide +kernel
      have hl : raw12921step1Labels = raw12921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12921step0 raw12921step0Labels permutation35 permutation7
    mixedMoment B raw12921step1 raw12921step1Labels = mixedMoment B raw12921step2 raw12921step2Labels := by
      have ha : raw12921step2 = raw12921step1 := by apply Matrix.ext; unfold raw12921step2 raw12921step1; decide +kernel
      have hl : raw12921step1Labels = labelEmbedding1 ∘ raw12921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12921step1 raw12921step1Labels raw12921step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw12922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12922 raw12922Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12922 raw12922Labels = mixedMoment B raw12922step0 raw12922step0Labels := by
      have hz : ∀ j, raw12922 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12922step0 = (fun i j => raw12922 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12922step0 raw12922; decide +kernel
      have hl : raw12922step0Labels = raw12922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12922 raw12922Labels permutation265 hz
    mixedMoment B raw12922step0 raw12922step0Labels = mixedMoment B raw12922step1 raw12922step1Labels := by
      have ha : raw12922step1 = (fun i j => raw12922step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12922step1 raw12922step0; decide +kernel
      have hl : raw12922step1Labels = raw12922step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12922step0 raw12922step0Labels permutation35 permutation7
    mixedMoment B raw12922step1 raw12922step1Labels = mixedMoment B raw12922step2 raw12922step2Labels := by
      have ha : raw12922step2 = raw12922step1 := by apply Matrix.ext; unfold raw12922step2 raw12922step1; decide +kernel
      have hl : raw12922step1Labels = labelEmbedding1 ∘ raw12922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12922step1 raw12922step1Labels raw12922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12923 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12923 raw12923Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw12923 raw12923Labels = mixedMoment B raw12923step0 raw12923step0Labels := by
      have hz : ∀ j, raw12923 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12923step0 = (fun i j => raw12923 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12923step0 raw12923; decide +kernel
      have hl : raw12923step0Labels = raw12923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12923 raw12923Labels permutation265 hz
    mixedMoment B raw12923step0 raw12923step0Labels = mixedMoment B raw12923step1 raw12923step1Labels := by
      have ha : raw12923step1 = (fun i j => raw12923step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12923step1 raw12923step0; decide +kernel
      have hl : raw12923step1Labels = raw12923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12923step0 raw12923step0Labels permutation97 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw12924 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12924 raw12924Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw12924 raw12924Labels = mixedMoment B raw12924step0 raw12924step0Labels := by
      have hz : ∀ j, raw12924 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12924step0 = (fun i j => raw12924 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12924step0 raw12924; decide +kernel
      have hl : raw12924step0Labels = raw12924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12924 raw12924Labels permutation265 hz
    mixedMoment B raw12924step0 raw12924step0Labels = mixedMoment B raw12924step1 raw12924step1Labels := by
      have ha : raw12924step1 = (fun i j => raw12924step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12924step1 raw12924step0; decide +kernel
      have hl : raw12924step1Labels = raw12924step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12924step0 raw12924step0Labels permutation36 permutation2
    mixedMoment B raw12924step1 raw12924step1Labels = mixedMoment B raw12924step2 raw12924step2Labels := by
      have ha : raw12924step2 = -raw12924step1 := by apply Matrix.ext; change ∀ i j, raw12924step2 i j = -(raw12924step1 i j); unfold raw12924step2 raw12924step1; decide +kernel
      have hl : raw12924step2Labels = raw12924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3380 node3380Labels := by rfl

def raw12925 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12925 raw12925Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw12925 raw12925Labels = mixedMoment B raw12925step0 raw12925step0Labels := by
      have hz : ∀ j, raw12925 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12925step0 = (fun i j => raw12925 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12925step0 raw12925; decide +kernel
      have hl : raw12925step0Labels = raw12925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12925 raw12925Labels permutation265 hz
    mixedMoment B raw12925step0 raw12925step0Labels = mixedMoment B raw12925step1 raw12925step1Labels := by
      have ha : raw12925step1 = (fun i j => raw12925step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12925step1 raw12925step0; decide +kernel
      have hl : raw12925step1Labels = raw12925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12925step0 raw12925step0Labels permutation35 permutation2
    mixedMoment B raw12925step1 raw12925step1Labels = mixedMoment B raw12925step2 raw12925step2Labels := by
      have ha : raw12925step2 = -raw12925step1 := by apply Matrix.ext; change ∀ i j, raw12925step2 i j = -(raw12925step1 i j); unfold raw12925step2 raw12925step1; decide +kernel
      have hl : raw12925step2Labels = raw12925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw12926 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw12926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12926 raw12926Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw12926 raw12926Labels = mixedMoment B raw12926step0 raw12926step0Labels := by
      have ha : raw12926step0 = (fun i j => raw12926 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12926step0 raw12926; decide +kernel
      have hl : raw12926step0Labels = raw12926Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12926 raw12926Labels permutation213 permutation4
    mixedMoment B raw12926step0 raw12926step0Labels = mixedMoment B raw12926step1 raw12926step1Labels := by
      have ha : raw12926step1 = -raw12926step0 := by apply Matrix.ext; change ∀ i j, raw12926step1 i j = -(raw12926step0 i j); unfold raw12926step1 raw12926step0; decide +kernel
      have hl : raw12926step1Labels = raw12926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw12927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12927 raw12927Labels = mixedMoment B node2926 node2926Labels := by
  calc
    mixedMoment B raw12927 raw12927Labels = mixedMoment B raw12927step0 raw12927step0Labels := by
      have ha : raw12927step0 = (fun i j => raw12927 (permutation501 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12927step0 raw12927; decide +kernel
      have hl : raw12927step0Labels = raw12927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12927 raw12927Labels permutation501 permutation2
    _ = mixedMoment B node2926 node2926Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
