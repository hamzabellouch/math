import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12544 raw12544Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12544 raw12544Labels = mixedMoment B raw12544step0 raw12544step0Labels := by
      have hz : ∀ j, raw12544 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12544step0 = (fun i j => raw12544 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12544step0 raw12544; decide +kernel
      have hl : raw12544step0Labels = raw12544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12544 raw12544Labels permutation520 hz
    mixedMoment B raw12544step0 raw12544step0Labels = mixedMoment B raw12544step1 raw12544step1Labels := by
      have hz : ∀ j, raw12544step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12544step1 = (fun i j => raw12544step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12544step1 raw12544step0; decide +kernel
      have hl : raw12544step1Labels = raw12544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12544step0 raw12544step0Labels permutation56 hz
    mixedMoment B raw12544step1 raw12544step1Labels = mixedMoment B raw12544step2 raw12544step2Labels := by
      have ha : raw12544step2 = (fun i j => raw12544step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12544step2 raw12544step1; decide +kernel
      have hl : raw12544step2Labels = raw12544step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12544step1 raw12544step1Labels permutation10 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw12545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12545 raw12545Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12545 raw12545Labels = mixedMoment B raw12545step0 raw12545step0Labels := by
      have hz : ∀ j, raw12545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12545step0 = (fun i j => raw12545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12545step0 raw12545; decide +kernel
      have hl : raw12545step0Labels = raw12545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12545 raw12545Labels permutation265 hz
    mixedMoment B raw12545step0 raw12545step0Labels = mixedMoment B raw12545step1 raw12545step1Labels := by
      have ha : raw12545step1 = (fun i j => raw12545step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12545step1 raw12545step0; decide +kernel
      have hl : raw12545step1Labels = raw12545step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12545step0 raw12545step0Labels permutation53 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12546step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12546 raw12546Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw12546 raw12546Labels = mixedMoment B raw12546step0 raw12546step0Labels := by
      have hz : ∀ j, raw12546 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12546step0 = (fun i j => raw12546 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12546step0 raw12546; decide +kernel
      have hl : raw12546step0Labels = raw12546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12546 raw12546Labels permutation265 hz
    mixedMoment B raw12546step0 raw12546step0Labels = mixedMoment B raw12546step1 raw12546step1Labels := by
      have ha : raw12546step1 = (fun i j => raw12546step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12546step1 raw12546step0; decide +kernel
      have hl : raw12546step1Labels = raw12546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12546step0 raw12546step0Labels permutation37 permutation3
    mixedMoment B raw12546step1 raw12546step1Labels = mixedMoment B raw12546step2 raw12546step2Labels := by
      have ha : raw12546step2 = raw12546step1 := by apply Matrix.ext; unfold raw12546step2 raw12546step1; decide +kernel
      have hl : raw12546step1Labels = labelEmbedding6 ∘ raw12546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12546step1 raw12546step1Labels raw12546step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw12547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12547 raw12547Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw12547 raw12547Labels = mixedMoment B raw12547step0 raw12547step0Labels := by
      have ha : raw12547step0 = (fun i j => raw12547 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12547step0 raw12547; decide +kernel
      have hl : raw12547step0Labels = raw12547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12547 raw12547Labels permutation155 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw12548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12548 raw12548Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw12548 raw12548Labels = mixedMoment B raw12548step0 raw12548step0Labels := by
      have hz : ∀ j, raw12548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12548step0 = (fun i j => raw12548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12548step0 raw12548; decide +kernel
      have hl : raw12548step0Labels = raw12548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12548 raw12548Labels permutation265 hz
    mixedMoment B raw12548step0 raw12548step0Labels = mixedMoment B raw12548step1 raw12548step1Labels := by
      have ha : raw12548step1 = (fun i j => raw12548step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12548step1 raw12548step0; decide +kernel
      have hl : raw12548step1Labels = raw12548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12548step0 raw12548step0Labels permutation35 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw12549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12549 raw12549Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw12549 raw12549Labels = mixedMoment B raw12549step0 raw12549step0Labels := by
      have hz : ∀ j, raw12549 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12549step0 = (fun i j => raw12549 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12549step0 raw12549; decide +kernel
      have hl : raw12549step0Labels = raw12549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12549 raw12549Labels permutation520 hz
    mixedMoment B raw12549step0 raw12549step0Labels = mixedMoment B raw12549step1 raw12549step1Labels := by
      have hz : ∀ j, raw12549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12549step1 = (fun i j => raw12549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12549step1 raw12549step0; decide +kernel
      have hl : raw12549step1Labels = raw12549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12549step0 raw12549step0Labels permutation56 hz
    mixedMoment B raw12549step1 raw12549step1Labels = mixedMoment B raw12549step2 raw12549step2Labels := by
      have ha : raw12549step2 = (fun i j => raw12549step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12549step2 raw12549step1; decide +kernel
      have hl : raw12549step2Labels = raw12549step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12549step1 raw12549step1Labels permutation9 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw12550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12550 raw12550Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw12550 raw12550Labels = mixedMoment B raw12550step0 raw12550step0Labels := by
      have hz : ∀ j, raw12550 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12550step0 = (fun i j => raw12550 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12550step0 raw12550; decide +kernel
      have hl : raw12550step0Labels = raw12550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12550 raw12550Labels permutation265 hz
    mixedMoment B raw12550step0 raw12550step0Labels = mixedMoment B raw12550step1 raw12550step1Labels := by
      have ha : raw12550step1 = (fun i j => raw12550step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12550step1 raw12550step0; decide +kernel
      have hl : raw12550step1Labels = raw12550step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12550step0 raw12550step0Labels permutation37 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw12551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12551step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12551 raw12551Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw12551 raw12551Labels = mixedMoment B raw12551step0 raw12551step0Labels := by
      have hz : ∀ j, raw12551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12551step0 = (fun i j => raw12551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12551step0 raw12551; decide +kernel
      have hl : raw12551step0Labels = raw12551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12551 raw12551Labels permutation265 hz
    mixedMoment B raw12551step0 raw12551step0Labels = mixedMoment B raw12551step1 raw12551step1Labels := by
      have ha : raw12551step1 = (fun i j => raw12551step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12551step1 raw12551step0; decide +kernel
      have hl : raw12551step1Labels = raw12551step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12551step0 raw12551step0Labels permutation36 permutation3
    mixedMoment B raw12551step1 raw12551step1Labels = mixedMoment B raw12551step2 raw12551step2Labels := by
      have ha : raw12551step2 = raw12551step1 := by apply Matrix.ext; unfold raw12551step2 raw12551step1; decide +kernel
      have hl : raw12551step1Labels = labelEmbedding6 ∘ raw12551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12551step1 raw12551step1Labels raw12551step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw12552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12552 raw12552Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw12552 raw12552Labels = mixedMoment B raw12552step0 raw12552step0Labels := by
      have ha : raw12552step0 = (fun i j => raw12552 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12552step0 raw12552; decide +kernel
      have hl : raw12552step0Labels = raw12552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12552 raw12552Labels permutation153 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw12553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12553 raw12553Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw12553 raw12553Labels = mixedMoment B raw12553step0 raw12553step0Labels := by
      have hz : ∀ j, raw12553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12553step0 = (fun i j => raw12553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12553step0 raw12553; decide +kernel
      have hl : raw12553step0Labels = raw12553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12553 raw12553Labels permutation265 hz
    mixedMoment B raw12553step0 raw12553step0Labels = mixedMoment B raw12553step1 raw12553step1Labels := by
      have ha : raw12553step1 = (fun i j => raw12553step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12553step1 raw12553step0; decide +kernel
      have hl : raw12553step1Labels = raw12553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12553step0 raw12553step0Labels permutation33 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw12554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12554step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12554 raw12554Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw12554 raw12554Labels = mixedMoment B raw12554step0 raw12554step0Labels := by
      have hz : ∀ j, raw12554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12554step0 = (fun i j => raw12554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12554step0 raw12554; decide +kernel
      have hl : raw12554step0Labels = raw12554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12554 raw12554Labels permutation434 hz
    mixedMoment B raw12554step0 raw12554step0Labels = mixedMoment B raw12554step1 raw12554step1Labels := by
      have hz : ∀ j, raw12554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12554step1 = (fun i j => raw12554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12554step1 raw12554step0; decide +kernel
      have hl : raw12554step1Labels = raw12554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12554step0 raw12554step0Labels permutation56 hz
    mixedMoment B raw12554step1 raw12554step1Labels = mixedMoment B raw12554step2 raw12554step2Labels := by
      have ha : raw12554step2 = (fun i j => raw12554step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12554step2 raw12554step1; decide +kernel
      have hl : raw12554step2Labels = raw12554step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12554step1 raw12554step1Labels permutation9 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw12555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12555 raw12555Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw12555 raw12555Labels = mixedMoment B raw12555step0 raw12555step0Labels := by
      have hz : ∀ j, raw12555 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12555step0 = (fun i j => raw12555 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12555step0 raw12555; decide +kernel
      have hl : raw12555step0Labels = raw12555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12555 raw12555Labels permutation265 hz
    mixedMoment B raw12555step0 raw12555step0Labels = mixedMoment B raw12555step1 raw12555step1Labels := by
      have ha : raw12555step1 = (fun i j => raw12555step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12555step1 raw12555step0; decide +kernel
      have hl : raw12555step1Labels = raw12555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12555step0 raw12555step0Labels permutation36 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw12556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12556step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12556 raw12556Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw12556 raw12556Labels = mixedMoment B raw12556step0 raw12556step0Labels := by
      have hz : ∀ j, raw12556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12556step0 = (fun i j => raw12556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12556step0 raw12556; decide +kernel
      have hl : raw12556step0Labels = raw12556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12556 raw12556Labels permutation265 hz
    mixedMoment B raw12556step0 raw12556step0Labels = mixedMoment B raw12556step1 raw12556step1Labels := by
      have ha : raw12556step1 = (fun i j => raw12556step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12556step1 raw12556step0; decide +kernel
      have hl : raw12556step1Labels = raw12556step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12556step0 raw12556step0Labels permutation32 permutation3
    mixedMoment B raw12556step1 raw12556step1Labels = mixedMoment B raw12556step2 raw12556step2Labels := by
      have ha : raw12556step2 = raw12556step1 := by apply Matrix.ext; unfold raw12556step2 raw12556step1; decide +kernel
      have hl : raw12556step1Labels = labelEmbedding6 ∘ raw12556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12556step1 raw12556step1Labels raw12556step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw12557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12557 raw12557Labels = mixedMoment B node5148 node5148Labels := by
  calc
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw12558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12558 raw12558Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw12558 raw12558Labels = mixedMoment B raw12558step0 raw12558step0Labels := by
      have hz : ∀ j, raw12558 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12558step0 = (fun i j => raw12558 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12558step0 raw12558; decide +kernel
      have hl : raw12558step0Labels = raw12558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12558 raw12558Labels permutation265 hz
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw12559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12559 raw12559Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12559 raw12559Labels = mixedMoment B raw12559step0 raw12559step0Labels := by
      have hz : ∀ j, raw12559 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12559step0 = (fun i j => raw12559 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12559step0 raw12559; decide +kernel
      have hl : raw12559step0Labels = raw12559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12559 raw12559Labels permutation434 hz
    mixedMoment B raw12559step0 raw12559step0Labels = mixedMoment B raw12559step1 raw12559step1Labels := by
      have hz : ∀ j, raw12559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12559step1 = (fun i j => raw12559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12559step1 raw12559step0; decide +kernel
      have hl : raw12559step1Labels = raw12559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12559step0 raw12559step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw12560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12560 raw12560Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12560 raw12560Labels = mixedMoment B raw12560step0 raw12560step0Labels := by
      have hz : ∀ j, raw12560 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12560step0 = (fun i j => raw12560 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12560step0 raw12560; decide +kernel
      have hl : raw12560step0Labels = raw12560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12560 raw12560Labels permutation520 hz
    mixedMoment B raw12560step0 raw12560step0Labels = mixedMoment B raw12560step1 raw12560step1Labels := by
      have hz : ∀ j, raw12560step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12560step1 = (fun i j => raw12560step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12560step1 raw12560step0; decide +kernel
      have hl : raw12560step1Labels = raw12560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12560step0 raw12560step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12561 raw12561Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw12561 raw12561Labels = mixedMoment B raw12561step0 raw12561step0Labels := by
      have ha : raw12561step0 = (fun i j => raw12561 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12561step0 raw12561; decide +kernel
      have hl : raw12561step0Labels = raw12561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12561 raw12561Labels permutation156 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw12562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12562 raw12562Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw12562 raw12562Labels = mixedMoment B raw12562step0 raw12562step0Labels := by
      have hz : ∀ j, raw12562 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12562step0 = (fun i j => raw12562 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12562step0 raw12562; decide +kernel
      have hl : raw12562step0Labels = raw12562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12562 raw12562Labels permutation265 hz
    mixedMoment B raw12562step0 raw12562step0Labels = mixedMoment B raw12562step1 raw12562step1Labels := by
      have ha : raw12562step1 = (fun i j => raw12562step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12562step1 raw12562step0; decide +kernel
      have hl : raw12562step1Labels = raw12562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12562step0 raw12562step0Labels permutation36 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw12563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12563 raw12563Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw12563 raw12563Labels = mixedMoment B raw12563step0 raw12563step0Labels := by
      have hz : ∀ j, raw12563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12563step0 = (fun i j => raw12563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12563step0 raw12563; decide +kernel
      have hl : raw12563step0Labels = raw12563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12563 raw12563Labels permutation434 hz
    mixedMoment B raw12563step0 raw12563step0Labels = mixedMoment B raw12563step1 raw12563step1Labels := by
      have hz : ∀ j, raw12563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12563step1 = (fun i j => raw12563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12563step1 raw12563step0; decide +kernel
      have hl : raw12563step1Labels = raw12563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12563step0 raw12563step0Labels permutation56 hz
    mixedMoment B raw12563step1 raw12563step1Labels = mixedMoment B raw12563step2 raw12563step2Labels := by
      have ha : raw12563step2 = (fun i j => raw12563step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12563step2 raw12563step1; decide +kernel
      have hl : raw12563step2Labels = raw12563step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12563step1 raw12563step1Labels permutation9 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw12564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12564 raw12564Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw12564 raw12564Labels = mixedMoment B raw12564step0 raw12564step0Labels := by
      have hz : ∀ j, raw12564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12564step0 = (fun i j => raw12564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12564step0 raw12564; decide +kernel
      have hl : raw12564step0Labels = raw12564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12564 raw12564Labels permutation520 hz
    mixedMoment B raw12564step0 raw12564step0Labels = mixedMoment B raw12564step1 raw12564step1Labels := by
      have hz : ∀ j, raw12564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12564step1 = (fun i j => raw12564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12564step1 raw12564step0; decide +kernel
      have hl : raw12564step1Labels = raw12564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12564step0 raw12564step0Labels permutation56 hz
    mixedMoment B raw12564step1 raw12564step1Labels = mixedMoment B raw12564step2 raw12564step2Labels := by
      have ha : raw12564step2 = (fun i j => raw12564step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12564step2 raw12564step1; decide +kernel
      have hl : raw12564step2Labels = raw12564step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12564step1 raw12564step1Labels permutation9 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw12565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12565 raw12565Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw12565 raw12565Labels = mixedMoment B raw12565step0 raw12565step0Labels := by
      have hz : ∀ j, raw12565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12565step0 = (fun i j => raw12565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12565step0 raw12565; decide +kernel
      have hl : raw12565step0Labels = raw12565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12565 raw12565Labels permutation265 hz
    mixedMoment B raw12565step0 raw12565step0Labels = mixedMoment B raw12565step1 raw12565step1Labels := by
      have ha : raw12565step1 = (fun i j => raw12565step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12565step1 raw12565step0; decide +kernel
      have hl : raw12565step1Labels = raw12565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12565step0 raw12565step0Labels permutation36 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw12566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12566 raw12566Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw12566 raw12566Labels = mixedMoment B raw12566step0 raw12566step0Labels := by
      have ha : raw12566step0 = (fun i j => raw12566 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12566step0 raw12566; decide +kernel
      have hl : raw12566step0Labels = raw12566Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12566 raw12566Labels permutation194 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw12567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12567 raw12567Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw12567 raw12567Labels = mixedMoment B raw12567step0 raw12567step0Labels := by
      have ha : raw12567step0 = (fun i j => raw12567 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12567step0 raw12567; decide +kernel
      have hl : raw12567step0Labels = raw12567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12567 raw12567Labels permutation194 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw12568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12568 raw12568Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw12568 raw12568Labels = mixedMoment B raw12568step0 raw12568step0Labels := by
      have hz : ∀ j, raw12568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12568step0 = (fun i j => raw12568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12568step0 raw12568; decide +kernel
      have hl : raw12568step0Labels = raw12568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12568 raw12568Labels permutation434 hz
    mixedMoment B raw12568step0 raw12568step0Labels = mixedMoment B raw12568step1 raw12568step1Labels := by
      have ha : raw12568step1 = (fun i j => raw12568step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12568step1 raw12568step0; decide +kernel
      have hl : raw12568step1Labels = raw12568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12568step0 raw12568step0Labels permutation42 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw12569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12569 raw12569Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw12569 raw12569Labels = mixedMoment B raw12569step0 raw12569step0Labels := by
      have hz : ∀ j, raw12569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12569step0 = (fun i j => raw12569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12569step0 raw12569; decide +kernel
      have hl : raw12569step0Labels = raw12569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12569 raw12569Labels permutation520 hz
    mixedMoment B raw12569step0 raw12569step0Labels = mixedMoment B raw12569step1 raw12569step1Labels := by
      have ha : raw12569step1 = (fun i j => raw12569step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12569step1 raw12569step0; decide +kernel
      have hl : raw12569step1Labels = raw12569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12569step0 raw12569step0Labels permutation42 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw12570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12570 raw12570Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw12570 raw12570Labels = mixedMoment B raw12570step0 raw12570step0Labels := by
      have ha : raw12570step0 = (fun i j => raw12570 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12570step0 raw12570; decide +kernel
      have hl : raw12570step0Labels = raw12570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12570 raw12570Labels permutation194 permutation3
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw12571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12571 raw12571Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw12571 raw12571Labels = mixedMoment B raw12571step0 raw12571step0Labels := by
      have hz : ∀ j, raw12571 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12571step0 = (fun i j => raw12571 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12571step0 raw12571; decide +kernel
      have hl : raw12571step0Labels = raw12571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12571 raw12571Labels permutation265 hz
    mixedMoment B raw12571step0 raw12571step0Labels = mixedMoment B raw12571step1 raw12571step1Labels := by
      have ha : raw12571step1 = (fun i j => raw12571step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12571step1 raw12571step0; decide +kernel
      have hl : raw12571step1Labels = raw12571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12571step0 raw12571step0Labels permutation36 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw12572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12572 raw12572Labels = mixedMoment B node2958 node2958Labels := by
  calc
    mixedMoment B raw12572 raw12572Labels = mixedMoment B raw12572step0 raw12572step0Labels := by
      have ha : raw12572step0 = (fun i j => raw12572 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12572step0 raw12572; decide +kernel
      have hl : raw12572step0Labels = raw12572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12572 raw12572Labels permutation156 permutation3
    _ = mixedMoment B node2958 node2958Labels := by rfl

def raw12573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12573 raw12573Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw12573 raw12573Labels = mixedMoment B raw12573step0 raw12573step0Labels := by
      have hz : ∀ j, raw12573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12573step0 = (fun i j => raw12573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12573step0 raw12573; decide +kernel
      have hl : raw12573step0Labels = raw12573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12573 raw12573Labels permutation434 hz
    mixedMoment B raw12573step0 raw12573step0Labels = mixedMoment B raw12573step1 raw12573step1Labels := by
      have hz : ∀ j, raw12573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12573step1 = (fun i j => raw12573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12573step1 raw12573step0; decide +kernel
      have hl : raw12573step1Labels = raw12573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12573step0 raw12573step0Labels permutation56 hz
    mixedMoment B raw12573step1 raw12573step1Labels = mixedMoment B raw12573step2 raw12573step2Labels := by
      have ha : raw12573step2 = (fun i j => raw12573step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12573step2 raw12573step1; decide +kernel
      have hl : raw12573step2Labels = raw12573step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12573step1 raw12573step1Labels permutation9 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw12574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12574step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12574 raw12574Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw12574 raw12574Labels = mixedMoment B raw12574step0 raw12574step0Labels := by
      have hz : ∀ j, raw12574 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12574step0 = (fun i j => raw12574 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12574step0 raw12574; decide +kernel
      have hl : raw12574step0Labels = raw12574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12574 raw12574Labels permutation520 hz
    mixedMoment B raw12574step0 raw12574step0Labels = mixedMoment B raw12574step1 raw12574step1Labels := by
      have hz : ∀ j, raw12574step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12574step1 = (fun i j => raw12574step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12574step1 raw12574step0; decide +kernel
      have hl : raw12574step1Labels = raw12574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12574step0 raw12574step0Labels permutation56 hz
    mixedMoment B raw12574step1 raw12574step1Labels = mixedMoment B raw12574step2 raw12574step2Labels := by
      have ha : raw12574step2 = (fun i j => raw12574step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12574step2 raw12574step1; decide +kernel
      have hl : raw12574step2Labels = raw12574step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12574step1 raw12574step1Labels permutation9 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw12575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12575 raw12575Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw12575 raw12575Labels = mixedMoment B raw12575step0 raw12575step0Labels := by
      have hz : ∀ j, raw12575 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12575step0 = (fun i j => raw12575 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12575step0 raw12575; decide +kernel
      have hl : raw12575step0Labels = raw12575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12575 raw12575Labels permutation265 hz
    mixedMoment B raw12575step0 raw12575step0Labels = mixedMoment B raw12575step1 raw12575step1Labels := by
      have ha : raw12575step1 = (fun i j => raw12575step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12575step1 raw12575step0; decide +kernel
      have hl : raw12575step1Labels = raw12575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12575step0 raw12575step0Labels permutation50 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw12576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12576 raw12576Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw12576 raw12576Labels = mixedMoment B raw12576step0 raw12576step0Labels := by
      have hz : ∀ j, raw12576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12576step0 = (fun i j => raw12576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12576step0 raw12576; decide +kernel
      have hl : raw12576step0Labels = raw12576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12576 raw12576Labels permutation265 hz
    mixedMoment B raw12576step0 raw12576step0Labels = mixedMoment B raw12576step1 raw12576step1Labels := by
      have ha : raw12576step1 = (fun i j => raw12576step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12576step1 raw12576step0; decide +kernel
      have hl : raw12576step1Labels = raw12576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12576step0 raw12576step0Labels permutation37 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw12577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12577 raw12577Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw12577 raw12577Labels = mixedMoment B raw12577step0 raw12577step0Labels := by
      have ha : raw12577step0 = (fun i j => raw12577 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12577step0 raw12577; decide +kernel
      have hl : raw12577step0Labels = raw12577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12577 raw12577Labels permutation157 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw12578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12578 raw12578Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw12578 raw12578Labels = mixedMoment B raw12578step0 raw12578step0Labels := by
      have hz : ∀ j, raw12578 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12578step0 = (fun i j => raw12578 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12578step0 raw12578; decide +kernel
      have hl : raw12578step0Labels = raw12578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12578 raw12578Labels permutation265 hz
    mixedMoment B raw12578step0 raw12578step0Labels = mixedMoment B raw12578step1 raw12578step1Labels := by
      have ha : raw12578step1 = (fun i j => raw12578step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12578step1 raw12578step0; decide +kernel
      have hl : raw12578step1Labels = raw12578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12578step0 raw12578step0Labels permutation37 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw12579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw12579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12579 raw12579Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw12579 raw12579Labels = mixedMoment B raw12579step0 raw12579step0Labels := by
      have hz : ∀ j, raw12579 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12579step0 = (fun i j => raw12579 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12579step0 raw12579; decide +kernel
      have hl : raw12579step0Labels = raw12579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12579 raw12579Labels permutation520 hz
    mixedMoment B raw12579step0 raw12579step0Labels = mixedMoment B raw12579step1 raw12579step1Labels := by
      have hz : ∀ j, raw12579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12579step1 = (fun i j => raw12579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12579step1 raw12579step0; decide +kernel
      have hl : raw12579step1Labels = raw12579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12579step0 raw12579step0Labels permutation56 hz
    mixedMoment B raw12579step1 raw12579step1Labels = mixedMoment B raw12579step2 raw12579step2Labels := by
      have ha : raw12579step2 = (fun i j => raw12579step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12579step2 raw12579step1; decide +kernel
      have hl : raw12579step2Labels = raw12579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12579step1 raw12579step1Labels permutation9 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw12580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw12580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12580 raw12580Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw12580 raw12580Labels = mixedMoment B raw12580step0 raw12580step0Labels := by
      have hz : ∀ j, raw12580 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12580step0 = (fun i j => raw12580 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12580step0 raw12580; decide +kernel
      have hl : raw12580step0Labels = raw12580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12580 raw12580Labels permutation265 hz
    mixedMoment B raw12580step0 raw12580step0Labels = mixedMoment B raw12580step1 raw12580step1Labels := by
      have ha : raw12580step1 = (fun i j => raw12580step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12580step1 raw12580step0; decide +kernel
      have hl : raw12580step1Labels = raw12580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12580step0 raw12580step0Labels permutation37 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw12581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12581 raw12581Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw12581 raw12581Labels = mixedMoment B raw12581step0 raw12581step0Labels := by
      have hz : ∀ j, raw12581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12581step0 = (fun i j => raw12581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12581step0 raw12581; decide +kernel
      have hl : raw12581step0Labels = raw12581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12581 raw12581Labels permutation265 hz
    mixedMoment B raw12581step0 raw12581step0Labels = mixedMoment B raw12581step1 raw12581step1Labels := by
      have ha : raw12581step1 = (fun i j => raw12581step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12581step1 raw12581step0; decide +kernel
      have hl : raw12581step1Labels = raw12581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12581step0 raw12581step0Labels permutation36 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw12582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12582 raw12582Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw12582 raw12582Labels = mixedMoment B raw12582step0 raw12582step0Labels := by
      have ha : raw12582step0 = (fun i j => raw12582 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12582step0 raw12582; decide +kernel
      have hl : raw12582step0Labels = raw12582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12582 raw12582Labels permutation156 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw12583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw12583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12583 raw12583Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw12583 raw12583Labels = mixedMoment B raw12583step0 raw12583step0Labels := by
      have hz : ∀ j, raw12583 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12583step0 = (fun i j => raw12583 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12583step0 raw12583; decide +kernel
      have hl : raw12583step0Labels = raw12583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12583 raw12583Labels permutation265 hz
    mixedMoment B raw12583step0 raw12583step0Labels = mixedMoment B raw12583step1 raw12583step1Labels := by
      have ha : raw12583step1 = (fun i j => raw12583step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12583step1 raw12583step0; decide +kernel
      have hl : raw12583step1Labels = raw12583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12583step0 raw12583step0Labels permutation36 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw12584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw12584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw12584step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12584 raw12584Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw12584 raw12584Labels = mixedMoment B raw12584step0 raw12584step0Labels := by
      have hz : ∀ j, raw12584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12584step0 = (fun i j => raw12584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12584step0 raw12584; decide +kernel
      have hl : raw12584step0Labels = raw12584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12584 raw12584Labels permutation434 hz
    mixedMoment B raw12584step0 raw12584step0Labels = mixedMoment B raw12584step1 raw12584step1Labels := by
      have hz : ∀ j, raw12584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12584step1 = (fun i j => raw12584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12584step1 raw12584step0; decide +kernel
      have hl : raw12584step1Labels = raw12584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12584step0 raw12584step0Labels permutation56 hz
    mixedMoment B raw12584step1 raw12584step1Labels = mixedMoment B raw12584step2 raw12584step2Labels := by
      have ha : raw12584step2 = (fun i j => raw12584step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12584step2 raw12584step1; decide +kernel
      have hl : raw12584step2Labels = raw12584step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12584step1 raw12584step1Labels permutation9 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw12585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw12585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw12585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12585 raw12585Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw12585 raw12585Labels = mixedMoment B raw12585step0 raw12585step0Labels := by
      have hz : ∀ j, raw12585 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12585step0 = (fun i j => raw12585 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12585step0 raw12585; decide +kernel
      have hl : raw12585step0Labels = raw12585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12585 raw12585Labels permutation265 hz
    mixedMoment B raw12585step0 raw12585step0Labels = mixedMoment B raw12585step1 raw12585step1Labels := by
      have ha : raw12585step1 = (fun i j => raw12585step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12585step1 raw12585step0; decide +kernel
      have hl : raw12585step1Labels = raw12585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12585step0 raw12585step0Labels permutation36 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw12586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12586 raw12586Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw12586 raw12586Labels = mixedMoment B raw12586step0 raw12586step0Labels := by
      have hz : ∀ j, raw12586 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12586step0 = (fun i j => raw12586 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12586step0 raw12586; decide +kernel
      have hl : raw12586step0Labels = raw12586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12586 raw12586Labels permutation265 hz
    mixedMoment B raw12586step0 raw12586step0Labels = mixedMoment B raw12586step1 raw12586step1Labels := by
      have ha : raw12586step1 = (fun i j => raw12586step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12586step1 raw12586step0; decide +kernel
      have hl : raw12586step1Labels = raw12586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12586step0 raw12586step0Labels permutation32 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw12587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12587 raw12587Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw12587 raw12587Labels = mixedMoment B raw12587step0 raw12587step0Labels := by
      have ha : raw12587step0 = (fun i j => raw12587 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12587step0 raw12587; decide +kernel
      have hl : raw12587step0Labels = raw12587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12587 raw12587Labels permutation152 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw12588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12588 raw12588Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw12588 raw12588Labels = mixedMoment B raw12588step0 raw12588step0Labels := by
      have hz : ∀ j, raw12588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12588step0 = (fun i j => raw12588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12588step0 raw12588; decide +kernel
      have hl : raw12588step0Labels = raw12588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12588 raw12588Labels permutation265 hz
    mixedMoment B raw12588step0 raw12588step0Labels = mixedMoment B raw12588step1 raw12588step1Labels := by
      have ha : raw12588step1 = (fun i j => raw12588step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12588step1 raw12588step0; decide +kernel
      have hl : raw12588step1Labels = raw12588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12588step0 raw12588step0Labels permutation32 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw12589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12589 raw12589Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw12589 raw12589Labels = mixedMoment B raw12589step0 raw12589step0Labels := by
      have hz : ∀ j, raw12589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw12589step0 = (fun i j => raw12589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw12589step0 raw12589; decide +kernel
      have hl : raw12589step0Labels = raw12589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12589 raw12589Labels permutation434 hz
    mixedMoment B raw12589step0 raw12589step0Labels = mixedMoment B raw12589step1 raw12589step1Labels := by
      have hz : ∀ j, raw12589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12589step1 = (fun i j => raw12589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12589step1 raw12589step0; decide +kernel
      have hl : raw12589step1Labels = raw12589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12589step0 raw12589step0Labels permutation56 hz
    mixedMoment B raw12589step1 raw12589step1Labels = mixedMoment B raw12589step2 raw12589step2Labels := by
      have ha : raw12589step2 = (fun i j => raw12589step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12589step2 raw12589step1; decide +kernel
      have hl : raw12589step2Labels = raw12589step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12589step1 raw12589step1Labels permutation8 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw12590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw12590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12590 raw12590Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw12590 raw12590Labels = mixedMoment B raw12590step0 raw12590step0Labels := by
      have hz : ∀ j, raw12590 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12590step0 = (fun i j => raw12590 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12590step0 raw12590; decide +kernel
      have hl : raw12590step0Labels = raw12590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12590 raw12590Labels permutation520 hz
    mixedMoment B raw12590step0 raw12590step0Labels = mixedMoment B raw12590step1 raw12590step1Labels := by
      have hz : ∀ j, raw12590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12590step1 = (fun i j => raw12590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12590step1 raw12590step0; decide +kernel
      have hl : raw12590step1Labels = raw12590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12590step0 raw12590step0Labels permutation56 hz
    mixedMoment B raw12590step1 raw12590step1Labels = mixedMoment B raw12590step2 raw12590step2Labels := by
      have ha : raw12590step2 = (fun i j => raw12590step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12590step2 raw12590step1; decide +kernel
      have hl : raw12590step2Labels = raw12590step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12590step1 raw12590step1Labels permutation8 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw12591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12591 raw12591Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw12591 raw12591Labels = mixedMoment B raw12591step0 raw12591step0Labels := by
      have ha : raw12591step0 = (fun i j => raw12591 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12591step0 raw12591; decide +kernel
      have hl : raw12591step0Labels = raw12591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12591 raw12591Labels permutation152 permutation3
    mixedMoment B raw12591step0 raw12591step0Labels = mixedMoment B raw12591step1 raw12591step1Labels := by
      have ha : raw12591step1 = raw12591step0 := by apply Matrix.ext; unfold raw12591step1 raw12591step0; decide +kernel
      have hl : raw12591step0Labels = labelEmbedding6 ∘ raw12591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12591step0 raw12591step0Labels raw12591step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw12592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12592 raw12592Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw12592 raw12592Labels = mixedMoment B raw12592step0 raw12592step0Labels := by
      have hz : ∀ j, raw12592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12592step0 = (fun i j => raw12592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12592step0 raw12592; decide +kernel
      have hl : raw12592step0Labels = raw12592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12592 raw12592Labels permutation265 hz
    mixedMoment B raw12592step0 raw12592step0Labels = mixedMoment B raw12592step1 raw12592step1Labels := by
      have ha : raw12592step1 = (fun i j => raw12592step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12592step1 raw12592step0; decide +kernel
      have hl : raw12592step1Labels = raw12592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12592step0 raw12592step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw12593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12593 raw12593Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw12593 raw12593Labels = mixedMoment B raw12593step0 raw12593step0Labels := by
      have hz : ∀ j, raw12593 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12593step0 = (fun i j => raw12593 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12593step0 raw12593; decide +kernel
      have hl : raw12593step0Labels = raw12593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12593 raw12593Labels permutation265 hz
    mixedMoment B raw12593step0 raw12593step0Labels = mixedMoment B raw12593step1 raw12593step1Labels := by
      have ha : raw12593step1 = (fun i j => raw12593step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12593step1 raw12593step0; decide +kernel
      have hl : raw12593step1Labels = raw12593step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12593step0 raw12593step0Labels permutation33 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw12594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12594 raw12594Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw12594 raw12594Labels = mixedMoment B raw12594step0 raw12594step0Labels := by
      have hz : ∀ j, raw12594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12594step0 = (fun i j => raw12594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12594step0 raw12594; decide +kernel
      have hl : raw12594step0Labels = raw12594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12594 raw12594Labels permutation265 hz
    mixedMoment B raw12594step0 raw12594step0Labels = mixedMoment B raw12594step1 raw12594step1Labels := by
      have ha : raw12594step1 = (fun i j => raw12594step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12594step1 raw12594step0; decide +kernel
      have hl : raw12594step1Labels = raw12594step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12594step0 raw12594step0Labels permutation35 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw12595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12595 raw12595Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw12595 raw12595Labels = mixedMoment B raw12595step0 raw12595step0Labels := by
      have hz : ∀ j, raw12595 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12595step0 = (fun i j => raw12595 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12595step0 raw12595; decide +kernel
      have hl : raw12595step0Labels = raw12595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12595 raw12595Labels permutation590 hz
    mixedMoment B raw12595step0 raw12595step0Labels = mixedMoment B raw12595step1 raw12595step1Labels := by
      have hz : ∀ j, raw12595step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12595step1 = (fun i j => raw12595step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12595step1 raw12595step0; decide +kernel
      have hl : raw12595step1Labels = raw12595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12595step0 raw12595step0Labels permutation56 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw12596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12596 raw12596Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw12596 raw12596Labels = mixedMoment B raw12596step0 raw12596step0Labels := by
      have ha : raw12596step0 = (fun i j => raw12596 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12596step0 raw12596; decide +kernel
      have hl : raw12596step0Labels = raw12596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12596 raw12596Labels permutation184 permutation3
    mixedMoment B raw12596step0 raw12596step0Labels = mixedMoment B raw12596step1 raw12596step1Labels := by
      have ha : raw12596step1 = raw12596step0 := by apply Matrix.ext; unfold raw12596step1 raw12596step0; decide +kernel
      have hl : raw12596step0Labels = labelEmbedding6 ∘ raw12596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12596step0 raw12596step0Labels raw12596step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw12597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12597 raw12597Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw12597 raw12597Labels = mixedMoment B raw12597step0 raw12597step0Labels := by
      have ha : raw12597step0 = (fun i j => raw12597 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12597step0 raw12597; decide +kernel
      have hl : raw12597step0Labels = raw12597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12597 raw12597Labels permutation184 permutation3
    mixedMoment B raw12597step0 raw12597step0Labels = mixedMoment B raw12597step1 raw12597step1Labels := by
      have ha : raw12597step1 = raw12597step0 := by apply Matrix.ext; unfold raw12597step1 raw12597step0; decide +kernel
      have hl : raw12597step0Labels = labelEmbedding6 ∘ raw12597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12597step0 raw12597step0Labels raw12597step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw12598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12598 raw12598Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw12598 raw12598Labels = mixedMoment B raw12598step0 raw12598step0Labels := by
      have ha : raw12598step0 = (fun i j => raw12598 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12598step0 raw12598; decide +kernel
      have hl : raw12598step0Labels = raw12598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12598 raw12598Labels permutation208 permutation3
    mixedMoment B raw12598step0 raw12598step0Labels = mixedMoment B raw12598step1 raw12598step1Labels := by
      have ha : raw12598step1 = raw12598step0 := by apply Matrix.ext; unfold raw12598step1 raw12598step0; decide +kernel
      have hl : raw12598step0Labels = labelEmbedding6 ∘ raw12598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12598step0 raw12598step0Labels raw12598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw12599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12599 raw12599Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw12599 raw12599Labels = mixedMoment B raw12599step0 raw12599step0Labels := by
      have ha : raw12599step0 = (fun i j => raw12599 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12599step0 raw12599; decide +kernel
      have hl : raw12599step0Labels = raw12599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12599 raw12599Labels permutation232 permutation3
    mixedMoment B raw12599step0 raw12599step0Labels = mixedMoment B raw12599step1 raw12599step1Labels := by
      have ha : raw12599step1 = raw12599step0 := by apply Matrix.ext; unfold raw12599step1 raw12599step0; decide +kernel
      have hl : raw12599step0Labels = labelEmbedding6 ∘ raw12599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12599step0 raw12599step0Labels raw12599step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw12600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12600step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12600 raw12600Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12600 raw12600Labels = mixedMoment B raw12600step0 raw12600step0Labels := by
      have hz : ∀ j, raw12600 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12600step0 = (fun i j => raw12600 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12600step0 raw12600; decide +kernel
      have hl : raw12600step0Labels = raw12600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12600 raw12600Labels permutation590 hz
    mixedMoment B raw12600step0 raw12600step0Labels = mixedMoment B raw12600step1 raw12600step1Labels := by
      have ha : raw12600step1 = (fun i j => raw12600step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12600step1 raw12600step0; decide +kernel
      have hl : raw12600step1Labels = raw12600step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12600step0 raw12600step0Labels permutation41 permutation3
    mixedMoment B raw12600step1 raw12600step1Labels = mixedMoment B raw12600step2 raw12600step2Labels := by
      have ha : raw12600step2 = raw12600step1 := by apply Matrix.ext; unfold raw12600step2 raw12600step1; decide +kernel
      have hl : raw12600step1Labels = labelEmbedding6 ∘ raw12600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12600step1 raw12600step1Labels raw12600step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12601step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12601 raw12601Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw12601 raw12601Labels = mixedMoment B raw12601step0 raw12601step0Labels := by
      have hz : ∀ j, raw12601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12601step0 = (fun i j => raw12601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12601step0 raw12601; decide +kernel
      have hl : raw12601step0Labels = raw12601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12601 raw12601Labels permutation265 hz
    mixedMoment B raw12601step0 raw12601step0Labels = mixedMoment B raw12601step1 raw12601step1Labels := by
      have ha : raw12601step1 = (fun i j => raw12601step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12601step1 raw12601step0; decide +kernel
      have hl : raw12601step1Labels = raw12601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12601step0 raw12601step0Labels permutation41 permutation3
    mixedMoment B raw12601step1 raw12601step1Labels = mixedMoment B raw12601step2 raw12601step2Labels := by
      have ha : raw12601step2 = raw12601step1 := by apply Matrix.ext; unfold raw12601step2 raw12601step1; decide +kernel
      have hl : raw12601step1Labels = labelEmbedding6 ∘ raw12601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12601step1 raw12601step1Labels raw12601step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw12602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12602step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12602 raw12602Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw12602 raw12602Labels = mixedMoment B raw12602step0 raw12602step0Labels := by
      have ha : raw12602step0 = (fun i j => raw12602 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12602step0 raw12602; decide +kernel
      have hl : raw12602step0Labels = raw12602Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12602 raw12602Labels permutation161 permutation3
    mixedMoment B raw12602step0 raw12602step0Labels = mixedMoment B raw12602step1 raw12602step1Labels := by
      have ha : raw12602step1 = raw12602step0 := by apply Matrix.ext; unfold raw12602step1 raw12602step0; decide +kernel
      have hl : raw12602step0Labels = labelEmbedding6 ∘ raw12602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12602step0 raw12602step0Labels raw12602step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw12603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12603 raw12603Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12603 raw12603Labels = mixedMoment B raw12603step0 raw12603step0Labels := by
      have hz : ∀ j, raw12603 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12603step0 = (fun i j => raw12603 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12603step0 raw12603; decide +kernel
      have hl : raw12603step0Labels = raw12603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12603 raw12603Labels permutation265 hz
    mixedMoment B raw12603step0 raw12603step0Labels = mixedMoment B raw12603step1 raw12603step1Labels := by
      have ha : raw12603step1 = (fun i j => raw12603step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12603step1 raw12603step0; decide +kernel
      have hl : raw12603step1Labels = raw12603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12603step0 raw12603step0Labels permutation41 permutation3
    mixedMoment B raw12603step1 raw12603step1Labels = mixedMoment B raw12603step2 raw12603step2Labels := by
      have ha : raw12603step2 = raw12603step1 := by apply Matrix.ext; unfold raw12603step2 raw12603step1; decide +kernel
      have hl : raw12603step1Labels = labelEmbedding6 ∘ raw12603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12603step1 raw12603step1Labels raw12603step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12604 raw12604Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12604 raw12604Labels = mixedMoment B raw12604step0 raw12604step0Labels := by
      have hz : ∀ j, raw12604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12604step0 = (fun i j => raw12604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12604step0 raw12604; decide +kernel
      have hl : raw12604step0Labels = raw12604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12604 raw12604Labels permutation265 hz
    mixedMoment B raw12604step0 raw12604step0Labels = mixedMoment B raw12604step1 raw12604step1Labels := by
      have ha : raw12604step1 = (fun i j => raw12604step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12604step1 raw12604step0; decide +kernel
      have hl : raw12604step1Labels = raw12604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12604step0 raw12604step0Labels permutation47 permutation3
    mixedMoment B raw12604step1 raw12604step1Labels = mixedMoment B raw12604step2 raw12604step2Labels := by
      have ha : raw12604step2 = raw12604step1 := by apply Matrix.ext; unfold raw12604step2 raw12604step1; decide +kernel
      have hl : raw12604step1Labels = labelEmbedding6 ∘ raw12604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12604step1 raw12604step1Labels raw12604step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12605step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12605step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12605step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12605 raw12605Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw12605 raw12605Labels = mixedMoment B raw12605step0 raw12605step0Labels := by
      have hz : ∀ j, raw12605 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12605step0 = (fun i j => raw12605 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12605step0 raw12605; decide +kernel
      have hl : raw12605step0Labels = raw12605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12605 raw12605Labels permutation590 hz
    mixedMoment B raw12605step0 raw12605step0Labels = mixedMoment B raw12605step1 raw12605step1Labels := by
      have hz : ∀ j, raw12605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12605step1 = (fun i j => raw12605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12605step1 raw12605step0; decide +kernel
      have hl : raw12605step1Labels = raw12605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12605step0 raw12605step0Labels permutation56 hz
    mixedMoment B raw12605step1 raw12605step1Labels = mixedMoment B raw12605step2 raw12605step2Labels := by
      have ha : raw12605step2 = (fun i j => raw12605step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12605step2 raw12605step1; decide +kernel
      have hl : raw12605step2Labels = raw12605step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12605step1 raw12605step1Labels permutation11 permutation3
    mixedMoment B raw12605step2 raw12605step2Labels = mixedMoment B raw12605step3 raw12605step3Labels := by
      have ha : raw12605step3 = raw12605step2 := by apply Matrix.ext; unfold raw12605step3 raw12605step2; decide +kernel
      have hl : raw12605step2Labels = labelEmbedding6 ∘ raw12605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12605step2 raw12605step2Labels raw12605step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw12606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12606 raw12606Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw12606 raw12606Labels = mixedMoment B raw12606step0 raw12606step0Labels := by
      have hz : ∀ j, raw12606 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12606step0 = (fun i j => raw12606 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12606step0 raw12606; decide +kernel
      have hl : raw12606step0Labels = raw12606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12606 raw12606Labels permutation265 hz
    mixedMoment B raw12606step0 raw12606step0Labels = mixedMoment B raw12606step1 raw12606step1Labels := by
      have ha : raw12606step1 = (fun i j => raw12606step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12606step1 raw12606step0; decide +kernel
      have hl : raw12606step1Labels = raw12606step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12606step0 raw12606step0Labels permutation35 permutation3
    mixedMoment B raw12606step1 raw12606step1Labels = mixedMoment B raw12606step2 raw12606step2Labels := by
      have ha : raw12606step2 = raw12606step1 := by apply Matrix.ext; unfold raw12606step2 raw12606step1; decide +kernel
      have hl : raw12606step1Labels = labelEmbedding6 ∘ raw12606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12606step1 raw12606step1Labels raw12606step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw12607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12607 raw12607Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw12607 raw12607Labels = mixedMoment B raw12607step0 raw12607step0Labels := by
      have ha : raw12607step0 = (fun i j => raw12607 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12607step0 raw12607; decide +kernel
      have hl : raw12607step0Labels = raw12607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12607 raw12607Labels permutation155 permutation3
    mixedMoment B raw12607step0 raw12607step0Labels = mixedMoment B raw12607step1 raw12607step1Labels := by
      have ha : raw12607step1 = raw12607step0 := by apply Matrix.ext; unfold raw12607step1 raw12607step0; decide +kernel
      have hl : raw12607step0Labels = labelEmbedding6 ∘ raw12607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12607step0 raw12607step0Labels raw12607step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw12608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12608 raw12608Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw12608 raw12608Labels = mixedMoment B raw12608step0 raw12608step0Labels := by
      have hz : ∀ j, raw12608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12608step0 = (fun i j => raw12608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12608step0 raw12608; decide +kernel
      have hl : raw12608step0Labels = raw12608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12608 raw12608Labels permutation265 hz
    mixedMoment B raw12608step0 raw12608step0Labels = mixedMoment B raw12608step1 raw12608step1Labels := by
      have ha : raw12608step1 = (fun i j => raw12608step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12608step1 raw12608step0; decide +kernel
      have hl : raw12608step1Labels = raw12608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12608step0 raw12608step0Labels permutation35 permutation3
    mixedMoment B raw12608step1 raw12608step1Labels = mixedMoment B raw12608step2 raw12608step2Labels := by
      have ha : raw12608step2 = raw12608step1 := by apply Matrix.ext; unfold raw12608step2 raw12608step1; decide +kernel
      have hl : raw12608step1Labels = labelEmbedding6 ∘ raw12608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12608step1 raw12608step1Labels raw12608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw12609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12609 raw12609Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw12609 raw12609Labels = mixedMoment B raw12609step0 raw12609step0Labels := by
      have hz : ∀ j, raw12609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12609step0 = (fun i j => raw12609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12609step0 raw12609; decide +kernel
      have hl : raw12609step0Labels = raw12609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12609 raw12609Labels permutation265 hz
    mixedMoment B raw12609step0 raw12609step0Labels = mixedMoment B raw12609step1 raw12609step1Labels := by
      have ha : raw12609step1 = (fun i j => raw12609step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12609step1 raw12609step0; decide +kernel
      have hl : raw12609step1Labels = raw12609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12609step0 raw12609step0Labels permutation45 permutation3
    mixedMoment B raw12609step1 raw12609step1Labels = mixedMoment B raw12609step2 raw12609step2Labels := by
      have ha : raw12609step2 = raw12609step1 := by apply Matrix.ext; unfold raw12609step2 raw12609step1; decide +kernel
      have hl : raw12609step1Labels = labelEmbedding6 ∘ raw12609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12609step1 raw12609step1Labels raw12609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw12610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12610 raw12610Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12610 raw12610Labels = mixedMoment B raw12610step0 raw12610step0Labels := by
      have hz : ∀ j, raw12610 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12610step0 = (fun i j => raw12610 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12610step0 raw12610; decide +kernel
      have hl : raw12610step0Labels = raw12610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12610 raw12610Labels permutation590 hz
    mixedMoment B raw12610step0 raw12610step0Labels = mixedMoment B raw12610step1 raw12610step1Labels := by
      have hz : ∀ j, raw12610step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12610step1 = (fun i j => raw12610step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12610step1 raw12610step0; decide +kernel
      have hl : raw12610step1Labels = raw12610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12610step0 raw12610step0Labels permutation56 hz
    mixedMoment B raw12610step1 raw12610step1Labels = mixedMoment B raw12610step2 raw12610step2Labels := by
      have ha : raw12610step2 = (fun i j => raw12610step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12610step2 raw12610step1; decide +kernel
      have hl : raw12610step2Labels = raw12610step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12610step1 raw12610step1Labels permutation9 permutation3
    mixedMoment B raw12610step2 raw12610step2Labels = mixedMoment B raw12610step3 raw12610step3Labels := by
      have ha : raw12610step3 = raw12610step2 := by apply Matrix.ext; unfold raw12610step3 raw12610step2; decide +kernel
      have hl : raw12610step2Labels = labelEmbedding6 ∘ raw12610step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12610step2 raw12610step2Labels raw12610step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12611 raw12611Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw12611 raw12611Labels = mixedMoment B raw12611step0 raw12611step0Labels := by
      have hz : ∀ j, raw12611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12611step0 = (fun i j => raw12611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12611step0 raw12611; decide +kernel
      have hl : raw12611step0Labels = raw12611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12611 raw12611Labels permutation265 hz
    mixedMoment B raw12611step0 raw12611step0Labels = mixedMoment B raw12611step1 raw12611step1Labels := by
      have ha : raw12611step1 = (fun i j => raw12611step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12611step1 raw12611step0; decide +kernel
      have hl : raw12611step1Labels = raw12611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12611step0 raw12611step0Labels permutation33 permutation3
    mixedMoment B raw12611step1 raw12611step1Labels = mixedMoment B raw12611step2 raw12611step2Labels := by
      have ha : raw12611step2 = raw12611step1 := by apply Matrix.ext; unfold raw12611step2 raw12611step1; decide +kernel
      have hl : raw12611step1Labels = labelEmbedding6 ∘ raw12611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12611step1 raw12611step1Labels raw12611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw12612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12612step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12612step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12612 raw12612Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw12612 raw12612Labels = mixedMoment B raw12612step0 raw12612step0Labels := by
      have ha : raw12612step0 = (fun i j => raw12612 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12612step0 raw12612; decide +kernel
      have hl : raw12612step0Labels = raw12612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12612 raw12612Labels permutation153 permutation3
    mixedMoment B raw12612step0 raw12612step0Labels = mixedMoment B raw12612step1 raw12612step1Labels := by
      have ha : raw12612step1 = raw12612step0 := by apply Matrix.ext; unfold raw12612step1 raw12612step0; decide +kernel
      have hl : raw12612step0Labels = labelEmbedding6 ∘ raw12612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12612step0 raw12612step0Labels raw12612step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw12613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12613 raw12613Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw12613 raw12613Labels = mixedMoment B raw12613step0 raw12613step0Labels := by
      have hz : ∀ j, raw12613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12613step0 = (fun i j => raw12613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12613step0 raw12613; decide +kernel
      have hl : raw12613step0Labels = raw12613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12613 raw12613Labels permutation265 hz
    mixedMoment B raw12613step0 raw12613step0Labels = mixedMoment B raw12613step1 raw12613step1Labels := by
      have ha : raw12613step1 = (fun i j => raw12613step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12613step1 raw12613step0; decide +kernel
      have hl : raw12613step1Labels = raw12613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12613step0 raw12613step0Labels permutation33 permutation3
    mixedMoment B raw12613step1 raw12613step1Labels = mixedMoment B raw12613step2 raw12613step2Labels := by
      have ha : raw12613step2 = raw12613step1 := by apply Matrix.ext; unfold raw12613step2 raw12613step1; decide +kernel
      have hl : raw12613step1Labels = labelEmbedding6 ∘ raw12613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12613step1 raw12613step1Labels raw12613step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw12614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12614 raw12614Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw12614 raw12614Labels = mixedMoment B raw12614step0 raw12614step0Labels := by
      have hz : ∀ j, raw12614 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12614step0 = (fun i j => raw12614 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12614step0 raw12614; decide +kernel
      have hl : raw12614step0Labels = raw12614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12614 raw12614Labels permutation265 hz
    mixedMoment B raw12614step0 raw12614step0Labels = mixedMoment B raw12614step1 raw12614step1Labels := by
      have ha : raw12614step1 = (fun i j => raw12614step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12614step1 raw12614step0; decide +kernel
      have hl : raw12614step1Labels = raw12614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12614step0 raw12614step0Labels permutation39 permutation3
    mixedMoment B raw12614step1 raw12614step1Labels = mixedMoment B raw12614step2 raw12614step2Labels := by
      have ha : raw12614step2 = raw12614step1 := by apply Matrix.ext; unfold raw12614step2 raw12614step1; decide +kernel
      have hl : raw12614step1Labels = labelEmbedding6 ∘ raw12614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12614step1 raw12614step1Labels raw12614step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw12615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw12615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12615step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12615 raw12615Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw12615 raw12615Labels = mixedMoment B raw12615step0 raw12615step0Labels := by
      have hz : ∀ j, raw12615 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12615step0 = (fun i j => raw12615 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12615step0 raw12615; decide +kernel
      have hl : raw12615step0Labels = raw12615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12615 raw12615Labels permutation590 hz
    mixedMoment B raw12615step0 raw12615step0Labels = mixedMoment B raw12615step1 raw12615step1Labels := by
      have hz : ∀ j, raw12615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12615step1 = (fun i j => raw12615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12615step1 raw12615step0; decide +kernel
      have hl : raw12615step1Labels = raw12615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12615step0 raw12615step0Labels permutation56 hz
    mixedMoment B raw12615step1 raw12615step1Labels = mixedMoment B raw12615step2 raw12615step2Labels := by
      have ha : raw12615step2 = (fun i j => raw12615step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12615step2 raw12615step1; decide +kernel
      have hl : raw12615step2Labels = raw12615step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12615step1 raw12615step1Labels permutation8 permutation3
    mixedMoment B raw12615step2 raw12615step2Labels = mixedMoment B raw12615step3 raw12615step3Labels := by
      have ha : raw12615step3 = raw12615step2 := by apply Matrix.ext; unfold raw12615step3 raw12615step2; decide +kernel
      have hl : raw12615step2Labels = labelEmbedding6 ∘ raw12615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12615step2 raw12615step2Labels raw12615step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw12616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12616 raw12616Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw12616 raw12616Labels = mixedMoment B raw12616step0 raw12616step0Labels := by
      have hz : ∀ j, raw12616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12616step0 = (fun i j => raw12616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12616step0 raw12616; decide +kernel
      have hl : raw12616step0Labels = raw12616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12616 raw12616Labels permutation265 hz
    mixedMoment B raw12616step0 raw12616step0Labels = mixedMoment B raw12616step1 raw12616step1Labels := by
      have ha : raw12616step1 = (fun i j => raw12616step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12616step1 raw12616step0; decide +kernel
      have hl : raw12616step1Labels = raw12616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12616step0 raw12616step0Labels permutation32 permutation3
    mixedMoment B raw12616step1 raw12616step1Labels = mixedMoment B raw12616step2 raw12616step2Labels := by
      have ha : raw12616step2 = raw12616step1 := by apply Matrix.ext; unfold raw12616step2 raw12616step1; decide +kernel
      have hl : raw12616step1Labels = labelEmbedding6 ∘ raw12616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12616step1 raw12616step1Labels raw12616step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw12617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12617step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12617 raw12617Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw12617 raw12617Labels = mixedMoment B raw12617step0 raw12617step0Labels := by
      have ha : raw12617step0 = (fun i j => raw12617 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12617step0 raw12617; decide +kernel
      have hl : raw12617step0Labels = raw12617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12617 raw12617Labels permutation152 permutation3
    mixedMoment B raw12617step0 raw12617step0Labels = mixedMoment B raw12617step1 raw12617step1Labels := by
      have ha : raw12617step1 = raw12617step0 := by apply Matrix.ext; unfold raw12617step1 raw12617step0; decide +kernel
      have hl : raw12617step0Labels = labelEmbedding6 ∘ raw12617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12617step0 raw12617step0Labels raw12617step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw12618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12618 raw12618Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw12618 raw12618Labels = mixedMoment B raw12618step0 raw12618step0Labels := by
      have hz : ∀ j, raw12618 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12618step0 = (fun i j => raw12618 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12618step0 raw12618; decide +kernel
      have hl : raw12618step0Labels = raw12618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12618 raw12618Labels permutation265 hz
    mixedMoment B raw12618step0 raw12618step0Labels = mixedMoment B raw12618step1 raw12618step1Labels := by
      have ha : raw12618step1 = (fun i j => raw12618step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12618step1 raw12618step0; decide +kernel
      have hl : raw12618step1Labels = raw12618step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12618step0 raw12618step0Labels permutation32 permutation3
    mixedMoment B raw12618step1 raw12618step1Labels = mixedMoment B raw12618step2 raw12618step2Labels := by
      have ha : raw12618step2 = raw12618step1 := by apply Matrix.ext; unfold raw12618step2 raw12618step1; decide +kernel
      have hl : raw12618step1Labels = labelEmbedding6 ∘ raw12618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12618step1 raw12618step1Labels raw12618step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw12619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12619 raw12619Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw12619 raw12619Labels = mixedMoment B raw12619step0 raw12619step0Labels := by
      have hz : ∀ j, raw12619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12619step0 = (fun i j => raw12619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12619step0 raw12619; decide +kernel
      have hl : raw12619step0Labels = raw12619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12619 raw12619Labels permutation265 hz
    mixedMoment B raw12619step0 raw12619step0Labels = mixedMoment B raw12619step1 raw12619step1Labels := by
      have ha : raw12619step1 = (fun i j => raw12619step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12619step1 raw12619step0; decide +kernel
      have hl : raw12619step1Labels = raw12619step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12619step0 raw12619step0Labels permutation38 permutation3
    mixedMoment B raw12619step1 raw12619step1Labels = mixedMoment B raw12619step2 raw12619step2Labels := by
      have ha : raw12619step2 = raw12619step1 := by apply Matrix.ext; unfold raw12619step2 raw12619step1; decide +kernel
      have hl : raw12619step1Labels = labelEmbedding6 ∘ raw12619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12619step1 raw12619step1Labels raw12619step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw12620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12620 raw12620Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw12620 raw12620Labels = mixedMoment B raw12620step0 raw12620step0Labels := by
      have hz : ∀ j, raw12620 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12620step0 = (fun i j => raw12620 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12620step0 raw12620; decide +kernel
      have hl : raw12620step0Labels = raw12620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12620 raw12620Labels permutation265 hz
    mixedMoment B raw12620step0 raw12620step0Labels = mixedMoment B raw12620step1 raw12620step1Labels := by
      have ha : raw12620step1 = (fun i j => raw12620step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12620step1 raw12620step0; decide +kernel
      have hl : raw12620step1Labels = raw12620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12620step0 raw12620step0Labels permutation44 permutation3
    mixedMoment B raw12620step1 raw12620step1Labels = mixedMoment B raw12620step2 raw12620step2Labels := by
      have ha : raw12620step2 = raw12620step1 := by apply Matrix.ext; unfold raw12620step2 raw12620step1; decide +kernel
      have hl : raw12620step1Labels = labelEmbedding6 ∘ raw12620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12620step1 raw12620step1Labels raw12620step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw12621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12621 raw12621Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw12621 raw12621Labels = mixedMoment B raw12621step0 raw12621step0Labels := by
      have ha : raw12621step0 = (fun i j => raw12621 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12621step0 raw12621; decide +kernel
      have hl : raw12621step0Labels = raw12621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12621 raw12621Labels permutation152 permutation3
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw12622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12622 raw12622Labels = mixedMoment B node3999 node3999Labels := by
  calc
    mixedMoment B raw12622 raw12622Labels = mixedMoment B raw12622step0 raw12622step0Labels := by
      have hz : ∀ j, raw12622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12622step0 = (fun i j => raw12622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12622step0 raw12622; decide +kernel
      have hl : raw12622step0Labels = raw12622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12622 raw12622Labels permutation265 hz
    mixedMoment B raw12622step0 raw12622step0Labels = mixedMoment B raw12622step1 raw12622step1Labels := by
      have ha : raw12622step1 = (fun i j => raw12622step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12622step1 raw12622step0; decide +kernel
      have hl : raw12622step1Labels = raw12622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12622step0 raw12622step0Labels permutation32 permutation3
    _ = mixedMoment B node3999 node3999Labels := by rfl

def raw12623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12623 raw12623Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw12623 raw12623Labels = mixedMoment B raw12623step0 raw12623step0Labels := by
      have hz : ∀ j, raw12623 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12623step0 = (fun i j => raw12623 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12623step0 raw12623; decide +kernel
      have hl : raw12623step0Labels = raw12623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12623 raw12623Labels permutation265 hz
    mixedMoment B raw12623step0 raw12623step0Labels = mixedMoment B raw12623step1 raw12623step1Labels := by
      have ha : raw12623step1 = (fun i j => raw12623step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12623step1 raw12623step0; decide +kernel
      have hl : raw12623step1Labels = raw12623step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12623step0 raw12623step0Labels permutation38 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw12624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12624 raw12624Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw12624 raw12624Labels = mixedMoment B raw12624step0 raw12624step0Labels := by
      have hz : ∀ j, raw12624 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12624step0 = (fun i j => raw12624 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12624step0 raw12624; decide +kernel
      have hl : raw12624step0Labels = raw12624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12624 raw12624Labels permutation265 hz
    mixedMoment B raw12624step0 raw12624step0Labels = mixedMoment B raw12624step1 raw12624step1Labels := by
      have ha : raw12624step1 = (fun i j => raw12624step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12624step1 raw12624step0; decide +kernel
      have hl : raw12624step1Labels = raw12624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12624step0 raw12624step0Labels permutation44 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw12625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12625step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12625 raw12625Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw12625 raw12625Labels = mixedMoment B raw12625step0 raw12625step0Labels := by
      have hz : ∀ j, raw12625 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12625step0 = (fun i j => raw12625 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12625step0 raw12625; decide +kernel
      have hl : raw12625step0Labels = raw12625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12625 raw12625Labels permutation590 hz
    mixedMoment B raw12625step0 raw12625step0Labels = mixedMoment B raw12625step1 raw12625step1Labels := by
      have hz : ∀ j, raw12625step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12625step1 = (fun i j => raw12625step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12625step1 raw12625step0; decide +kernel
      have hl : raw12625step1Labels = raw12625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12625step0 raw12625step0Labels permutation56 hz
    mixedMoment B raw12625step1 raw12625step1Labels = mixedMoment B raw12625step2 raw12625step2Labels := by
      have ha : raw12625step2 = (fun i j => raw12625step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12625step2 raw12625step1; decide +kernel
      have hl : raw12625step2Labels = raw12625step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12625step1 raw12625step1Labels permutation8 permutation3
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw12626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12626 raw12626Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw12626 raw12626Labels = mixedMoment B raw12626step0 raw12626step0Labels := by
      have ha : raw12626step0 = (fun i j => raw12626 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12626step0 raw12626; decide +kernel
      have hl : raw12626step0Labels = raw12626Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12626 raw12626Labels permutation184 permutation3
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw12627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12627 raw12627Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw12627 raw12627Labels = mixedMoment B raw12627step0 raw12627step0Labels := by
      have ha : raw12627step0 = (fun i j => raw12627 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12627step0 raw12627; decide +kernel
      have hl : raw12627step0Labels = raw12627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12627 raw12627Labels permutation184 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw12628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12628 raw12628Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw12628 raw12628Labels = mixedMoment B raw12628step0 raw12628step0Labels := by
      have ha : raw12628step0 = (fun i j => raw12628 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12628step0 raw12628; decide +kernel
      have hl : raw12628step0Labels = raw12628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12628 raw12628Labels permutation208 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw12629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12629 raw12629Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw12629 raw12629Labels = mixedMoment B raw12629step0 raw12629step0Labels := by
      have ha : raw12629step0 = (fun i j => raw12629 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12629step0 raw12629; decide +kernel
      have hl : raw12629step0Labels = raw12629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12629 raw12629Labels permutation232 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw12630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12630 raw12630Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw12630 raw12630Labels = mixedMoment B raw12630step0 raw12630step0Labels := by
      have hz : ∀ j, raw12630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12630step0 = (fun i j => raw12630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12630step0 raw12630; decide +kernel
      have hl : raw12630step0Labels = raw12630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12630 raw12630Labels permutation590 hz
    mixedMoment B raw12630step0 raw12630step0Labels = mixedMoment B raw12630step1 raw12630step1Labels := by
      have ha : raw12630step1 = (fun i j => raw12630step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12630step1 raw12630step0; decide +kernel
      have hl : raw12630step1Labels = raw12630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12630step0 raw12630step0Labels permutation41 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw12631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12631 raw12631Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw12631 raw12631Labels = mixedMoment B raw12631step0 raw12631step0Labels := by
      have hz : ∀ j, raw12631 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12631step0 = (fun i j => raw12631 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12631step0 raw12631; decide +kernel
      have hl : raw12631step0Labels = raw12631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12631 raw12631Labels permutation265 hz
    mixedMoment B raw12631step0 raw12631step0Labels = mixedMoment B raw12631step1 raw12631step1Labels := by
      have ha : raw12631step1 = (fun i j => raw12631step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12631step1 raw12631step0; decide +kernel
      have hl : raw12631step1Labels = raw12631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12631step0 raw12631step0Labels permutation41 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw12632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12632 raw12632Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw12632 raw12632Labels = mixedMoment B raw12632step0 raw12632step0Labels := by
      have ha : raw12632step0 = (fun i j => raw12632 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12632step0 raw12632; decide +kernel
      have hl : raw12632step0Labels = raw12632Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12632 raw12632Labels permutation161 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw12633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12633 raw12633Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12633 raw12633Labels = mixedMoment B raw12633step0 raw12633step0Labels := by
      have hz : ∀ j, raw12633 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12633step0 = (fun i j => raw12633 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12633step0 raw12633; decide +kernel
      have hl : raw12633step0Labels = raw12633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12633 raw12633Labels permutation265 hz
    mixedMoment B raw12633step0 raw12633step0Labels = mixedMoment B raw12633step1 raw12633step1Labels := by
      have ha : raw12633step1 = (fun i j => raw12633step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12633step1 raw12633step0; decide +kernel
      have hl : raw12633step1Labels = raw12633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12633step0 raw12633step0Labels permutation41 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12634 raw12634Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12634 raw12634Labels = mixedMoment B raw12634step0 raw12634step0Labels := by
      have hz : ∀ j, raw12634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12634step0 = (fun i j => raw12634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12634step0 raw12634; decide +kernel
      have hl : raw12634step0Labels = raw12634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12634 raw12634Labels permutation265 hz
    mixedMoment B raw12634step0 raw12634step0Labels = mixedMoment B raw12634step1 raw12634step1Labels := by
      have ha : raw12634step1 = (fun i j => raw12634step0 (permutation47 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12634step1 raw12634step0; decide +kernel
      have hl : raw12634step1Labels = raw12634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12634step0 raw12634step0Labels permutation47 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12635 raw12635Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw12635 raw12635Labels = mixedMoment B raw12635step0 raw12635step0Labels := by
      have hz : ∀ j, raw12635 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12635step0 = (fun i j => raw12635 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12635step0 raw12635; decide +kernel
      have hl : raw12635step0Labels = raw12635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12635 raw12635Labels permutation590 hz
    mixedMoment B raw12635step0 raw12635step0Labels = mixedMoment B raw12635step1 raw12635step1Labels := by
      have hz : ∀ j, raw12635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12635step1 = (fun i j => raw12635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12635step1 raw12635step0; decide +kernel
      have hl : raw12635step1Labels = raw12635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12635step0 raw12635step0Labels permutation56 hz
    mixedMoment B raw12635step1 raw12635step1Labels = mixedMoment B raw12635step2 raw12635step2Labels := by
      have ha : raw12635step2 = (fun i j => raw12635step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12635step2 raw12635step1; decide +kernel
      have hl : raw12635step2Labels = raw12635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12635step1 raw12635step1Labels permutation11 permutation3
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw12636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12636 raw12636Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw12636 raw12636Labels = mixedMoment B raw12636step0 raw12636step0Labels := by
      have hz : ∀ j, raw12636 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12636step0 = (fun i j => raw12636 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12636step0 raw12636; decide +kernel
      have hl : raw12636step0Labels = raw12636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12636 raw12636Labels permutation265 hz
    mixedMoment B raw12636step0 raw12636step0Labels = mixedMoment B raw12636step1 raw12636step1Labels := by
      have ha : raw12636step1 = (fun i j => raw12636step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12636step1 raw12636step0; decide +kernel
      have hl : raw12636step1Labels = raw12636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12636step0 raw12636step0Labels permutation35 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw12637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12637 raw12637Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw12637 raw12637Labels = mixedMoment B raw12637step0 raw12637step0Labels := by
      have ha : raw12637step0 = (fun i j => raw12637 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12637step0 raw12637; decide +kernel
      have hl : raw12637step0Labels = raw12637Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12637 raw12637Labels permutation155 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw12638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw12638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12638 raw12638Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw12638 raw12638Labels = mixedMoment B raw12638step0 raw12638step0Labels := by
      have hz : ∀ j, raw12638 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12638step0 = (fun i j => raw12638 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12638step0 raw12638; decide +kernel
      have hl : raw12638step0Labels = raw12638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12638 raw12638Labels permutation265 hz
    mixedMoment B raw12638step0 raw12638step0Labels = mixedMoment B raw12638step1 raw12638step1Labels := by
      have ha : raw12638step1 = (fun i j => raw12638step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12638step1 raw12638step0; decide +kernel
      have hl : raw12638step1Labels = raw12638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12638step0 raw12638step0Labels permutation35 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw12639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw12639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12639 raw12639Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw12639 raw12639Labels = mixedMoment B raw12639step0 raw12639step0Labels := by
      have hz : ∀ j, raw12639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12639step0 = (fun i j => raw12639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12639step0 raw12639; decide +kernel
      have hl : raw12639step0Labels = raw12639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12639 raw12639Labels permutation265 hz
    mixedMoment B raw12639step0 raw12639step0Labels = mixedMoment B raw12639step1 raw12639step1Labels := by
      have ha : raw12639step1 = (fun i j => raw12639step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12639step1 raw12639step0; decide +kernel
      have hl : raw12639step1Labels = raw12639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12639step0 raw12639step0Labels permutation45 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw12640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw12640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw12640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12640 raw12640Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw12640 raw12640Labels = mixedMoment B raw12640step0 raw12640step0Labels := by
      have hz : ∀ j, raw12640 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12640step0 = (fun i j => raw12640 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12640step0 raw12640; decide +kernel
      have hl : raw12640step0Labels = raw12640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12640 raw12640Labels permutation590 hz
    mixedMoment B raw12640step0 raw12640step0Labels = mixedMoment B raw12640step1 raw12640step1Labels := by
      have hz : ∀ j, raw12640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12640step1 = (fun i j => raw12640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12640step1 raw12640step0; decide +kernel
      have hl : raw12640step1Labels = raw12640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12640step0 raw12640step0Labels permutation56 hz
    mixedMoment B raw12640step1 raw12640step1Labels = mixedMoment B raw12640step2 raw12640step2Labels := by
      have ha : raw12640step2 = (fun i j => raw12640step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12640step2 raw12640step1; decide +kernel
      have hl : raw12640step2Labels = raw12640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12640step1 raw12640step1Labels permutation9 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw12641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12641 raw12641Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw12641 raw12641Labels = mixedMoment B raw12641step0 raw12641step0Labels := by
      have hz : ∀ j, raw12641 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12641step0 = (fun i j => raw12641 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12641step0 raw12641; decide +kernel
      have hl : raw12641step0Labels = raw12641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12641 raw12641Labels permutation265 hz
    mixedMoment B raw12641step0 raw12641step0Labels = mixedMoment B raw12641step1 raw12641step1Labels := by
      have ha : raw12641step1 = (fun i j => raw12641step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12641step1 raw12641step0; decide +kernel
      have hl : raw12641step1Labels = raw12641step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12641step0 raw12641step0Labels permutation33 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw12642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12642 raw12642Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw12642 raw12642Labels = mixedMoment B raw12642step0 raw12642step0Labels := by
      have ha : raw12642step0 = (fun i j => raw12642 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12642step0 raw12642; decide +kernel
      have hl : raw12642step0Labels = raw12642Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12642 raw12642Labels permutation153 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw12643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12643 raw12643Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw12643 raw12643Labels = mixedMoment B raw12643step0 raw12643step0Labels := by
      have hz : ∀ j, raw12643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12643step0 = (fun i j => raw12643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12643step0 raw12643; decide +kernel
      have hl : raw12643step0Labels = raw12643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12643 raw12643Labels permutation265 hz
    mixedMoment B raw12643step0 raw12643step0Labels = mixedMoment B raw12643step1 raw12643step1Labels := by
      have ha : raw12643step1 = (fun i j => raw12643step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12643step1 raw12643step0; decide +kernel
      have hl : raw12643step1Labels = raw12643step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12643step0 raw12643step0Labels permutation33 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw12644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw12644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12644 raw12644Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw12644 raw12644Labels = mixedMoment B raw12644step0 raw12644step0Labels := by
      have hz : ∀ j, raw12644 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12644step0 = (fun i j => raw12644 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12644step0 raw12644; decide +kernel
      have hl : raw12644step0Labels = raw12644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12644 raw12644Labels permutation265 hz
    mixedMoment B raw12644step0 raw12644step0Labels = mixedMoment B raw12644step1 raw12644step1Labels := by
      have ha : raw12644step1 = (fun i j => raw12644step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12644step1 raw12644step0; decide +kernel
      have hl : raw12644step1Labels = raw12644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12644step0 raw12644step0Labels permutation39 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw12645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw12645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12645 raw12645Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw12645 raw12645Labels = mixedMoment B raw12645step0 raw12645step0Labels := by
      have hz : ∀ j, raw12645 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12645step0 = (fun i j => raw12645 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12645step0 raw12645; decide +kernel
      have hl : raw12645step0Labels = raw12645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12645 raw12645Labels permutation590 hz
    mixedMoment B raw12645step0 raw12645step0Labels = mixedMoment B raw12645step1 raw12645step1Labels := by
      have hz : ∀ j, raw12645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12645step1 = (fun i j => raw12645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12645step1 raw12645step0; decide +kernel
      have hl : raw12645step1Labels = raw12645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12645step0 raw12645step0Labels permutation56 hz
    mixedMoment B raw12645step1 raw12645step1Labels = mixedMoment B raw12645step2 raw12645step2Labels := by
      have ha : raw12645step2 = (fun i j => raw12645step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12645step2 raw12645step1; decide +kernel
      have hl : raw12645step2Labels = raw12645step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12645step1 raw12645step1Labels permutation8 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw12646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12646 raw12646Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw12646 raw12646Labels = mixedMoment B raw12646step0 raw12646step0Labels := by
      have hz : ∀ j, raw12646 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12646step0 = (fun i j => raw12646 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12646step0 raw12646; decide +kernel
      have hl : raw12646step0Labels = raw12646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12646 raw12646Labels permutation265 hz
    mixedMoment B raw12646step0 raw12646step0Labels = mixedMoment B raw12646step1 raw12646step1Labels := by
      have ha : raw12646step1 = (fun i j => raw12646step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12646step1 raw12646step0; decide +kernel
      have hl : raw12646step1Labels = raw12646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12646step0 raw12646step0Labels permutation32 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw12647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12647 raw12647Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw12647 raw12647Labels = mixedMoment B raw12647step0 raw12647step0Labels := by
      have ha : raw12647step0 = (fun i j => raw12647 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12647step0 raw12647; decide +kernel
      have hl : raw12647step0Labels = raw12647Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12647 raw12647Labels permutation152 permutation3
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw12648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12648 raw12648Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw12648 raw12648Labels = mixedMoment B raw12648step0 raw12648step0Labels := by
      have hz : ∀ j, raw12648 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12648step0 = (fun i j => raw12648 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12648step0 raw12648; decide +kernel
      have hl : raw12648step0Labels = raw12648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12648 raw12648Labels permutation265 hz
    mixedMoment B raw12648step0 raw12648step0Labels = mixedMoment B raw12648step1 raw12648step1Labels := by
      have ha : raw12648step1 = (fun i j => raw12648step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12648step1 raw12648step0; decide +kernel
      have hl : raw12648step1Labels = raw12648step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12648step0 raw12648step0Labels permutation32 permutation3
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw12649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12649 raw12649Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw12649 raw12649Labels = mixedMoment B raw12649step0 raw12649step0Labels := by
      have hz : ∀ j, raw12649 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12649step0 = (fun i j => raw12649 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12649step0 raw12649; decide +kernel
      have hl : raw12649step0Labels = raw12649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12649 raw12649Labels permutation265 hz
    mixedMoment B raw12649step0 raw12649step0Labels = mixedMoment B raw12649step1 raw12649step1Labels := by
      have ha : raw12649step1 = (fun i j => raw12649step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12649step1 raw12649step0; decide +kernel
      have hl : raw12649step1Labels = raw12649step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12649step0 raw12649step0Labels permutation38 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw12650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw12650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12650 raw12650Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw12650 raw12650Labels = mixedMoment B raw12650step0 raw12650step0Labels := by
      have hz : ∀ j, raw12650 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12650step0 = (fun i j => raw12650 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12650step0 raw12650; decide +kernel
      have hl : raw12650step0Labels = raw12650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12650 raw12650Labels permutation265 hz
    mixedMoment B raw12650step0 raw12650step0Labels = mixedMoment B raw12650step1 raw12650step1Labels := by
      have ha : raw12650step1 = (fun i j => raw12650step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12650step1 raw12650step0; decide +kernel
      have hl : raw12650step1Labels = raw12650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12650step0 raw12650step0Labels permutation44 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw12651 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12651step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12651 raw12651Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12651 raw12651Labels = mixedMoment B raw12651step0 raw12651step0Labels := by
      have hz : ∀ j, raw12651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12651step0 = (fun i j => raw12651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12651step0 raw12651; decide +kernel
      have hl : raw12651step0Labels = raw12651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12651 raw12651Labels permutation265 hz
    mixedMoment B raw12651step0 raw12651step0Labels = mixedMoment B raw12651step1 raw12651step1Labels := by
      have ha : raw12651step1 = (fun i j => raw12651step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12651step1 raw12651step0; decide +kernel
      have hl : raw12651step1Labels = raw12651step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12651step0 raw12651step0Labels permutation36 permutation7
    mixedMoment B raw12651step1 raw12651step1Labels = mixedMoment B raw12651step2 raw12651step2Labels := by
      have ha : raw12651step2 = raw12651step1 := by apply Matrix.ext; unfold raw12651step2 raw12651step1; decide +kernel
      have hl : raw12651step1Labels = labelEmbedding10 ∘ raw12651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12651step1 raw12651step1Labels raw12651step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12652step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12652 raw12652Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw12652 raw12652Labels = mixedMoment B raw12652step0 raw12652step0Labels := by
      have hz : ∀ j, raw12652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12652step0 = (fun i j => raw12652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12652step0 raw12652; decide +kernel
      have hl : raw12652step0Labels = raw12652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12652 raw12652Labels permutation265 hz
    mixedMoment B raw12652step0 raw12652step0Labels = mixedMoment B raw12652step1 raw12652step1Labels := by
      have ha : raw12652step1 = (fun i j => raw12652step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12652step1 raw12652step0; decide +kernel
      have hl : raw12652step1Labels = raw12652step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12652step0 raw12652step0Labels permutation32 permutation7
    mixedMoment B raw12652step1 raw12652step1Labels = mixedMoment B raw12652step2 raw12652step2Labels := by
      have ha : raw12652step2 = raw12652step1 := by apply Matrix.ext; unfold raw12652step2 raw12652step1; decide +kernel
      have hl : raw12652step1Labels = labelEmbedding10 ∘ raw12652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12652step1 raw12652step1Labels raw12652step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw12653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12653step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12653step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12653step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12653 raw12653Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw12653 raw12653Labels = mixedMoment B raw12653step0 raw12653step0Labels := by
      have ha : raw12653step0 = (fun i j => raw12653 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12653step0 raw12653; decide +kernel
      have hl : raw12653step0Labels = raw12653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12653 raw12653Labels permutation212 permutation4
    mixedMoment B raw12653step0 raw12653step0Labels = mixedMoment B raw12653step1 raw12653step1Labels := by
      have ha : raw12653step1 = -raw12653step0 := by apply Matrix.ext; change ∀ i j, raw12653step1 i j = -(raw12653step0 i j); unfold raw12653step1 raw12653step0; decide +kernel
      have hl : raw12653step1Labels = raw12653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12653step1 raw12653step1Labels = mixedMoment B raw12653step2 raw12653step2Labels := by
      have ha : raw12653step2 = raw12653step1 := by apply Matrix.ext; unfold raw12653step2 raw12653step1; decide +kernel
      have hl : raw12653step1Labels = labelEmbedding7 ∘ raw12653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12653step1 raw12653step1Labels raw12653step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw12654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12654step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12654 raw12654Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12654 raw12654Labels = mixedMoment B raw12654step0 raw12654step0Labels := by
      have ha : raw12654step0 = (fun i j => raw12654 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12654step0 raw12654; decide +kernel
      have hl : raw12654step0Labels = raw12654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12654 raw12654Labels permutation154 permutation6
    mixedMoment B raw12654step0 raw12654step0Labels = mixedMoment B raw12654step1 raw12654step1Labels := by
      have ha : raw12654step1 = raw12654step0 := by apply Matrix.ext; unfold raw12654step1 raw12654step0; decide +kernel
      have hl : raw12654step0Labels = labelEmbedding9 ∘ raw12654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12654step0 raw12654step0Labels raw12654step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw12655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12655 raw12655Labels = mixedMoment B node5283 node5283Labels := by
  calc
    mixedMoment B raw12655 raw12655Labels = mixedMoment B raw12655step0 raw12655step0Labels := by
      have ha : raw12655step0 = (fun i j => raw12655 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12655step0 raw12655; decide +kernel
      have hl : raw12655step0Labels = raw12655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12655 raw12655Labels permutation152 permutation6
    mixedMoment B raw12655step0 raw12655step0Labels = mixedMoment B raw12655step1 raw12655step1Labels := by
      have ha : raw12655step1 = raw12655step0 := by apply Matrix.ext; unfold raw12655step1 raw12655step0; decide +kernel
      have hl : raw12655step0Labels = labelEmbedding9 ∘ raw12655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12655step0 raw12655step0Labels raw12655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw12656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12656step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12656step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12656 raw12656Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw12656 raw12656Labels = mixedMoment B raw12656step0 raw12656step0Labels := by
      have hz : ∀ j, raw12656 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12656step0 = (fun i j => raw12656 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12656step0 raw12656; decide +kernel
      have hl : raw12656step0Labels = raw12656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12656 raw12656Labels permutation265 hz
    mixedMoment B raw12656step0 raw12656step0Labels = mixedMoment B raw12656step1 raw12656step1Labels := by
      have ha : raw12656step1 = (fun i j => raw12656step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12656step1 raw12656step0; decide +kernel
      have hl : raw12656step1Labels = raw12656step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12656step0 raw12656step0Labels permutation44 permutation4
    mixedMoment B raw12656step1 raw12656step1Labels = mixedMoment B raw12656step2 raw12656step2Labels := by
      have ha : raw12656step2 = -raw12656step1 := by apply Matrix.ext; change ∀ i j, raw12656step2 i j = -(raw12656step1 i j); unfold raw12656step2 raw12656step1; decide +kernel
      have hl : raw12656step2Labels = raw12656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12656step2 raw12656step2Labels = mixedMoment B raw12656step3 raw12656step3Labels := by
      have ha : raw12656step3 = raw12656step2 := by apply Matrix.ext; unfold raw12656step3 raw12656step2; decide +kernel
      have hl : raw12656step2Labels = labelEmbedding7 ∘ raw12656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12656step2 raw12656step2Labels raw12656step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw12657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12657step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12657 raw12657Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12657 raw12657Labels = mixedMoment B raw12657step0 raw12657step0Labels := by
      have hz : ∀ j, raw12657 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12657step0 = (fun i j => raw12657 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12657step0 raw12657; decide +kernel
      have hl : raw12657step0Labels = raw12657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12657 raw12657Labels permutation265 hz
    mixedMoment B raw12657step0 raw12657step0Labels = mixedMoment B raw12657step1 raw12657step1Labels := by
      have ha : raw12657step1 = (fun i j => raw12657step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12657step1 raw12657step0; decide +kernel
      have hl : raw12657step1Labels = raw12657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12657step0 raw12657step0Labels permutation34 permutation6
    mixedMoment B raw12657step1 raw12657step1Labels = mixedMoment B raw12657step2 raw12657step2Labels := by
      have ha : raw12657step2 = raw12657step1 := by apply Matrix.ext; unfold raw12657step2 raw12657step1; decide +kernel
      have hl : raw12657step1Labels = labelEmbedding9 ∘ raw12657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12657step1 raw12657step1Labels raw12657step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw12658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12658step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12658 raw12658Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12658 raw12658Labels = mixedMoment B raw12658step0 raw12658step0Labels := by
      have hz : ∀ j, raw12658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12658step0 = (fun i j => raw12658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12658step0 raw12658; decide +kernel
      have hl : raw12658step0Labels = raw12658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12658 raw12658Labels permutation265 hz
    mixedMoment B raw12658step0 raw12658step0Labels = mixedMoment B raw12658step1 raw12658step1Labels := by
      have ha : raw12658step1 = (fun i j => raw12658step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12658step1 raw12658step0; decide +kernel
      have hl : raw12658step1Labels = raw12658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12658step0 raw12658step0Labels permutation35 permutation6
    mixedMoment B raw12658step1 raw12658step1Labels = mixedMoment B raw12658step2 raw12658step2Labels := by
      have ha : raw12658step2 = raw12658step1 := by apply Matrix.ext; unfold raw12658step2 raw12658step1; decide +kernel
      have hl : raw12658step1Labels = labelEmbedding9 ∘ raw12658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12658step1 raw12658step1Labels raw12658step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12659step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12659step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12659step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12659 raw12659Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw12659 raw12659Labels = mixedMoment B raw12659step0 raw12659step0Labels := by
      have hz : ∀ j, raw12659 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12659step0 = (fun i j => raw12659 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12659step0 raw12659; decide +kernel
      have hl : raw12659step0Labels = raw12659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12659 raw12659Labels permutation265 hz
    mixedMoment B raw12659step0 raw12659step0Labels = mixedMoment B raw12659step1 raw12659step1Labels := by
      have ha : raw12659step1 = (fun i j => raw12659step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12659step1 raw12659step0; decide +kernel
      have hl : raw12659step1Labels = raw12659step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12659step0 raw12659step0Labels permutation38 permutation4
    mixedMoment B raw12659step1 raw12659step1Labels = mixedMoment B raw12659step2 raw12659step2Labels := by
      have ha : raw12659step2 = -raw12659step1 := by apply Matrix.ext; change ∀ i j, raw12659step2 i j = -(raw12659step1 i j); unfold raw12659step2 raw12659step1; decide +kernel
      have hl : raw12659step2Labels = raw12659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12659step2 raw12659step2Labels = mixedMoment B raw12659step3 raw12659step3Labels := by
      have ha : raw12659step3 = raw12659step2 := by apply Matrix.ext; unfold raw12659step3 raw12659step2; decide +kernel
      have hl : raw12659step2Labels = labelEmbedding7 ∘ raw12659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12659step2 raw12659step2Labels raw12659step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw12660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12660step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12660 raw12660Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12660 raw12660Labels = mixedMoment B raw12660step0 raw12660step0Labels := by
      have hz : ∀ j, raw12660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12660step0 = (fun i j => raw12660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12660step0 raw12660; decide +kernel
      have hl : raw12660step0Labels = raw12660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12660 raw12660Labels permutation265 hz
    mixedMoment B raw12660step0 raw12660step0Labels = mixedMoment B raw12660step1 raw12660step1Labels := by
      have ha : raw12660step1 = (fun i j => raw12660step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12660step1 raw12660step0; decide +kernel
      have hl : raw12660step1Labels = raw12660step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12660step0 raw12660step0Labels permutation33 permutation6
    mixedMoment B raw12660step1 raw12660step1Labels = mixedMoment B raw12660step2 raw12660step2Labels := by
      have ha : raw12660step2 = raw12660step1 := by apply Matrix.ext; unfold raw12660step2 raw12660step1; decide +kernel
      have hl : raw12660step1Labels = labelEmbedding9 ∘ raw12660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12660step1 raw12660step1Labels raw12660step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw12661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12661 raw12661Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw12661 raw12661Labels = mixedMoment B raw12661step0 raw12661step0Labels := by
      have hz : ∀ j, raw12661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12661step0 = (fun i j => raw12661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12661step0 raw12661; decide +kernel
      have hl : raw12661step0Labels = raw12661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12661 raw12661Labels permutation265 hz
    mixedMoment B raw12661step0 raw12661step0Labels = mixedMoment B raw12661step1 raw12661step1Labels := by
      have ha : raw12661step1 = (fun i j => raw12661step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12661step1 raw12661step0; decide +kernel
      have hl : raw12661step1Labels = raw12661step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12661step0 raw12661step0Labels permutation40 permutation4
    mixedMoment B raw12661step1 raw12661step1Labels = mixedMoment B raw12661step2 raw12661step2Labels := by
      have ha : raw12661step2 = -raw12661step1 := by apply Matrix.ext; change ∀ i j, raw12661step2 i j = -(raw12661step1 i j); unfold raw12661step2 raw12661step1; decide +kernel
      have hl : raw12661step2Labels = raw12661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw12662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12662 raw12662Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12662 raw12662Labels = mixedMoment B raw12662step0 raw12662step0Labels := by
      have hz : ∀ j, raw12662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12662step0 = (fun i j => raw12662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12662step0 raw12662; decide +kernel
      have hl : raw12662step0Labels = raw12662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12662 raw12662Labels permutation265 hz
    mixedMoment B raw12662step0 raw12662step0Labels = mixedMoment B raw12662step1 raw12662step1Labels := by
      have ha : raw12662step1 = (fun i j => raw12662step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12662step1 raw12662step0; decide +kernel
      have hl : raw12662step1Labels = raw12662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12662step0 raw12662step0Labels permutation36 permutation2
    mixedMoment B raw12662step1 raw12662step1Labels = mixedMoment B raw12662step2 raw12662step2Labels := by
      have ha : raw12662step2 = -raw12662step1 := by apply Matrix.ext; change ∀ i j, raw12662step2 i j = -(raw12662step1 i j); unfold raw12662step2 raw12662step1; decide +kernel
      have hl : raw12662step2Labels = raw12662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw12663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12663 raw12663Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw12663 raw12663Labels = mixedMoment B raw12663step0 raw12663step0Labels := by
      have hz : ∀ j, raw12663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12663step0 = (fun i j => raw12663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12663step0 raw12663; decide +kernel
      have hl : raw12663step0Labels = raw12663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12663 raw12663Labels permutation265 hz
    mixedMoment B raw12663step0 raw12663step0Labels = mixedMoment B raw12663step1 raw12663step1Labels := by
      have ha : raw12663step1 = -raw12663step0 := by apply Matrix.ext; change ∀ i j, raw12663step1 i j = -(raw12663step0 i j); unfold raw12663step1 raw12663step0; decide +kernel
      have hl : raw12663step1Labels = raw12663step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw12664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12664 raw12664Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw12664 raw12664Labels = mixedMoment B raw12664step0 raw12664step0Labels := by
      have ha : raw12664step0 = (fun i j => raw12664 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12664step0 raw12664; decide +kernel
      have hl : raw12664step0Labels = raw12664Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12664 raw12664Labels permutation212 permutation4
    mixedMoment B raw12664step0 raw12664step0Labels = mixedMoment B raw12664step1 raw12664step1Labels := by
      have ha : raw12664step1 = -raw12664step0 := by apply Matrix.ext; change ∀ i j, raw12664step1 i j = -(raw12664step0 i j); unfold raw12664step1 raw12664step0; decide +kernel
      have hl : raw12664step1Labels = raw12664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw12665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw12665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw12665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12665 raw12665Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw12665 raw12665Labels = mixedMoment B raw12665step0 raw12665step0Labels := by
      have hz : ∀ j, raw12665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12665step0 = (fun i j => raw12665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12665step0 raw12665; decide +kernel
      have hl : raw12665step0Labels = raw12665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12665 raw12665Labels permutation346 hz
    mixedMoment B raw12665step0 raw12665step0Labels = mixedMoment B raw12665step1 raw12665step1Labels := by
      have ha : raw12665step1 = (fun i j => raw12665step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12665step1 raw12665step0; decide +kernel
      have hl : raw12665step1Labels = raw12665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12665step0 raw12665step0Labels permutation40 permutation4
    mixedMoment B raw12665step1 raw12665step1Labels = mixedMoment B raw12665step2 raw12665step2Labels := by
      have ha : raw12665step2 = -raw12665step1 := by apply Matrix.ext; change ∀ i j, raw12665step2 i j = -(raw12665step1 i j); unfold raw12665step2 raw12665step1; decide +kernel
      have hl : raw12665step2Labels = raw12665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw12666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12666 raw12666Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12666 raw12666Labels = mixedMoment B raw12666step0 raw12666step0Labels := by
      have ha : raw12666step0 = (fun i j => raw12666 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12666step0 raw12666; decide +kernel
      have hl : raw12666step0Labels = raw12666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12666 raw12666Labels permutation234 permutation4
    mixedMoment B raw12666step0 raw12666step0Labels = mixedMoment B raw12666step1 raw12666step1Labels := by
      have ha : raw12666step1 = -raw12666step0 := by apply Matrix.ext; change ∀ i j, raw12666step1 i j = -(raw12666step0 i j); unfold raw12666step1 raw12666step0; decide +kernel
      have hl : raw12666step1Labels = raw12666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw12667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw12667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw12667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12667 raw12667Labels = mixedMoment B node3618 node3618Labels := by
  calc
    mixedMoment B raw12667 raw12667Labels = mixedMoment B raw12667step0 raw12667step0Labels := by
      have ha : raw12667step0 = (fun i j => raw12667 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12667step0 raw12667; decide +kernel
      have hl : raw12667step0Labels = raw12667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12667 raw12667Labels permutation216 permutation4
    mixedMoment B raw12667step0 raw12667step0Labels = mixedMoment B raw12667step1 raw12667step1Labels := by
      have ha : raw12667step1 = -raw12667step0 := by apply Matrix.ext; change ∀ i j, raw12667step1 i j = -(raw12667step0 i j); unfold raw12667step1 raw12667step0; decide +kernel
      have hl : raw12667step1Labels = raw12667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3618 node3618Labels := by rfl

def raw12668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12668step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12668 raw12668Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw12668 raw12668Labels = mixedMoment B raw12668step0 raw12668step0Labels := by
      have ha : raw12668step0 = (fun i j => raw12668 (permutation423 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12668step0 raw12668; decide +kernel
      have hl : raw12668step0Labels = raw12668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12668 raw12668Labels permutation423 permutation6
    mixedMoment B raw12668step0 raw12668step0Labels = mixedMoment B raw12668step1 raw12668step1Labels := by
      have ha : raw12668step1 = raw12668step0 := by apply Matrix.ext; unfold raw12668step1 raw12668step0; decide +kernel
      have hl : raw12668step0Labels = labelEmbedding9 ∘ raw12668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12668step0 raw12668step0Labels raw12668step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw12669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12669step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12669step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12669 raw12669Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw12669 raw12669Labels = mixedMoment B raw12669step0 raw12669step0Labels := by
      have hz : ∀ j, raw12669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12669step0 = (fun i j => raw12669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12669step0 raw12669; decide +kernel
      have hl : raw12669step0Labels = raw12669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12669 raw12669Labels permutation265 hz
    mixedMoment B raw12669step0 raw12669step0Labels = mixedMoment B raw12669step1 raw12669step1Labels := by
      have ha : raw12669step1 = (fun i j => raw12669step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12669step1 raw12669step0; decide +kernel
      have hl : raw12669step1Labels = raw12669step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12669step0 raw12669step0Labels permutation75 permutation4
    mixedMoment B raw12669step1 raw12669step1Labels = mixedMoment B raw12669step2 raw12669step2Labels := by
      have ha : raw12669step2 = -raw12669step1 := by apply Matrix.ext; change ∀ i j, raw12669step2 i j = -(raw12669step1 i j); unfold raw12669step2 raw12669step1; decide +kernel
      have hl : raw12669step2Labels = raw12669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12669step2 raw12669step2Labels = mixedMoment B raw12669step3 raw12669step3Labels := by
      have ha : raw12669step3 = raw12669step2 := by apply Matrix.ext; unfold raw12669step3 raw12669step2; decide +kernel
      have hl : raw12669step2Labels = labelEmbedding7 ∘ raw12669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12669step2 raw12669step2Labels raw12669step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw12670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12670step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12670 raw12670Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw12670 raw12670Labels = mixedMoment B raw12670step0 raw12670step0Labels := by
      have hz : ∀ j, raw12670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12670step0 = (fun i j => raw12670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12670step0 raw12670; decide +kernel
      have hl : raw12670step0Labels = raw12670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12670 raw12670Labels permutation265 hz
    mixedMoment B raw12670step0 raw12670step0Labels = mixedMoment B raw12670step1 raw12670step1Labels := by
      have ha : raw12670step1 = (fun i j => raw12670step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12670step1 raw12670step0; decide +kernel
      have hl : raw12670step1Labels = raw12670step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12670step0 raw12670step0Labels permutation79 permutation6
    mixedMoment B raw12670step1 raw12670step1Labels = mixedMoment B raw12670step2 raw12670step2Labels := by
      have ha : raw12670step2 = raw12670step1 := by apply Matrix.ext; unfold raw12670step2 raw12670step1; decide +kernel
      have hl : raw12670step1Labels = labelEmbedding9 ∘ raw12670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12670step1 raw12670step1Labels raw12670step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw12671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12671step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12671step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12671step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12671 raw12671Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw12671 raw12671Labels = mixedMoment B raw12671step0 raw12671step0Labels := by
      have hz : ∀ j, raw12671 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12671step0 = (fun i j => raw12671 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12671step0 raw12671; decide +kernel
      have hl : raw12671step0Labels = raw12671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12671 raw12671Labels permutation520 hz
    mixedMoment B raw12671step0 raw12671step0Labels = mixedMoment B raw12671step1 raw12671step1Labels := by
      have hz : ∀ j, raw12671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12671step1 = (fun i j => raw12671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12671step1 raw12671step0; decide +kernel
      have hl : raw12671step1Labels = raw12671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12671step0 raw12671step0Labels permutation56 hz
    mixedMoment B raw12671step1 raw12671step1Labels = mixedMoment B raw12671step2 raw12671step2Labels := by
      have ha : raw12671step2 = (fun i j => raw12671step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12671step2 raw12671step1; decide +kernel
      have hl : raw12671step2Labels = raw12671step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12671step1 raw12671step1Labels permutation19 permutation6
    mixedMoment B raw12671step2 raw12671step2Labels = mixedMoment B raw12671step3 raw12671step3Labels := by
      have ha : raw12671step3 = raw12671step2 := by apply Matrix.ext; unfold raw12671step3 raw12671step2; decide +kernel
      have hl : raw12671step2Labels = labelEmbedding9 ∘ raw12671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12671step2 raw12671step2Labels raw12671step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
