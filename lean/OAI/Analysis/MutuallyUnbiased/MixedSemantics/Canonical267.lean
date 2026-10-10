import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34176step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34176step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34176 raw34176Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw34176 raw34176Labels = mixedMoment B raw34176step0 raw34176step0Labels := by
      have hz : ∀ j, raw34176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34176step0 = (fun i j => raw34176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34176step0 raw34176; decide +kernel
      have hl : raw34176step0Labels = raw34176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34176 raw34176Labels permutation346 hz
    mixedMoment B raw34176step0 raw34176step0Labels = mixedMoment B raw34176step1 raw34176step1Labels := by
      have ha : raw34176step1 = (fun i j => raw34176step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34176step1 raw34176step0; decide +kernel
      have hl : raw34176step1Labels = raw34176step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34176step0 raw34176step0Labels permutation33 permutation3
    mixedMoment B raw34176step1 raw34176step1Labels = mixedMoment B raw34176step2 raw34176step2Labels := by
      have ha : raw34176step2 = raw34176step1 := by apply Matrix.ext; unfold raw34176step2 raw34176step1; decide +kernel
      have hl : raw34176step1Labels = labelEmbedding6 ∘ raw34176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34176step1 raw34176step1Labels raw34176step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw34177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34177step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34177 raw34177Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw34177 raw34177Labels = mixedMoment B raw34177step0 raw34177step0Labels := by
      have ha : raw34177step0 = (fun i j => raw34177 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34177step0 raw34177; decide +kernel
      have hl : raw34177step0Labels = raw34177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34177 raw34177Labels permutation177 permutation3
    mixedMoment B raw34177step0 raw34177step0Labels = mixedMoment B raw34177step1 raw34177step1Labels := by
      have ha : raw34177step1 = raw34177step0 := by apply Matrix.ext; unfold raw34177step1 raw34177step0; decide +kernel
      have hl : raw34177step0Labels = labelEmbedding6 ∘ raw34177step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34177step0 raw34177step0Labels raw34177step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

def raw34178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34178step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34178step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34178 raw34178Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34178 raw34178Labels = mixedMoment B raw34178step0 raw34178step0Labels := by
      have hz : ∀ j, raw34178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34178step0 = (fun i j => raw34178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34178step0 raw34178; decide +kernel
      have hl : raw34178step0Labels = raw34178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34178 raw34178Labels permutation346 hz
    mixedMoment B raw34178step0 raw34178step0Labels = mixedMoment B raw34178step1 raw34178step1Labels := by
      have ha : raw34178step1 = (fun i j => raw34178step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34178step1 raw34178step0; decide +kernel
      have hl : raw34178step1Labels = raw34178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34178step0 raw34178step0Labels permutation33 permutation3
    mixedMoment B raw34178step1 raw34178step1Labels = mixedMoment B raw34178step2 raw34178step2Labels := by
      have ha : raw34178step2 = raw34178step1 := by apply Matrix.ext; unfold raw34178step2 raw34178step1; decide +kernel
      have hl : raw34178step1Labels = labelEmbedding6 ∘ raw34178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34178step1 raw34178step1Labels raw34178step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw34179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw34179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34179step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34179step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34179 raw34179Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw34179 raw34179Labels = mixedMoment B raw34179step0 raw34179step0Labels := by
      have hz : ∀ j, raw34179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34179step0 = (fun i j => raw34179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34179step0 raw34179; decide +kernel
      have hl : raw34179step0Labels = raw34179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34179 raw34179Labels permutation346 hz
    mixedMoment B raw34179step0 raw34179step0Labels = mixedMoment B raw34179step1 raw34179step1Labels := by
      have ha : raw34179step1 = (fun i j => raw34179step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34179step1 raw34179step0; decide +kernel
      have hl : raw34179step1Labels = raw34179step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34179step0 raw34179step0Labels permutation36 permutation3
    mixedMoment B raw34179step1 raw34179step1Labels = mixedMoment B raw34179step2 raw34179step2Labels := by
      have ha : raw34179step2 = raw34179step1 := by apply Matrix.ext; unfold raw34179step2 raw34179step1; decide +kernel
      have hl : raw34179step1Labels = labelEmbedding6 ∘ raw34179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34179step1 raw34179step1Labels raw34179step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw34180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34180step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34180step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34180 raw34180Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw34180 raw34180Labels = mixedMoment B raw34180step0 raw34180step0Labels := by
      have hz : ∀ j, raw34180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34180step0 = (fun i j => raw34180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34180step0 raw34180; decide +kernel
      have hl : raw34180step0Labels = raw34180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34180 raw34180Labels permutation346 hz
    mixedMoment B raw34180step0 raw34180step0Labels = mixedMoment B raw34180step1 raw34180step1Labels := by
      have ha : raw34180step1 = (fun i j => raw34180step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34180step1 raw34180step0; decide +kernel
      have hl : raw34180step1Labels = raw34180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34180step0 raw34180step0Labels permutation34 permutation3
    mixedMoment B raw34180step1 raw34180step1Labels = mixedMoment B raw34180step2 raw34180step2Labels := by
      have ha : raw34180step2 = raw34180step1 := by apply Matrix.ext; unfold raw34180step2 raw34180step1; decide +kernel
      have hl : raw34180step1Labels = labelEmbedding6 ∘ raw34180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34180step1 raw34180step1Labels raw34180step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw34181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34181 raw34181Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw34181 raw34181Labels = mixedMoment B raw34181step0 raw34181step0Labels := by
      have hz : ∀ j, raw34181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34181step0 = (fun i j => raw34181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34181step0 raw34181; decide +kernel
      have hl : raw34181step0Labels = raw34181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34181 raw34181Labels permutation346 hz
    mixedMoment B raw34181step0 raw34181step0Labels = mixedMoment B raw34181step1 raw34181step1Labels := by
      have ha : raw34181step1 = (fun i j => raw34181step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34181step1 raw34181step0; decide +kernel
      have hl : raw34181step1Labels = raw34181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34181step0 raw34181step0Labels permutation34 permutation3
    mixedMoment B raw34181step1 raw34181step1Labels = mixedMoment B raw34181step2 raw34181step2Labels := by
      have ha : raw34181step2 = raw34181step1 := by apply Matrix.ext; unfold raw34181step2 raw34181step1; decide +kernel
      have hl : raw34181step1Labels = labelEmbedding6 ∘ raw34181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34181step1 raw34181step1Labels raw34181step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw34182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34182step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34182 raw34182Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw34182 raw34182Labels = mixedMoment B raw34182step0 raw34182step0Labels := by
      have ha : raw34182step0 = (fun i j => raw34182 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34182step0 raw34182; decide +kernel
      have hl : raw34182step0Labels = raw34182Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34182 raw34182Labels permutation178 permutation3
    mixedMoment B raw34182step0 raw34182step0Labels = mixedMoment B raw34182step1 raw34182step1Labels := by
      have ha : raw34182step1 = raw34182step0 := by apply Matrix.ext; unfold raw34182step1 raw34182step0; decide +kernel
      have hl : raw34182step0Labels = labelEmbedding6 ∘ raw34182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34182step0 raw34182step0Labels raw34182step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw34183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw34183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34183 raw34183Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw34183 raw34183Labels = mixedMoment B raw34183step0 raw34183step0Labels := by
      have hz : ∀ j, raw34183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34183step0 = (fun i j => raw34183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34183step0 raw34183; decide +kernel
      have hl : raw34183step0Labels = raw34183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34183 raw34183Labels permutation346 hz
    mixedMoment B raw34183step0 raw34183step0Labels = mixedMoment B raw34183step1 raw34183step1Labels := by
      have ha : raw34183step1 = (fun i j => raw34183step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34183step1 raw34183step0; decide +kernel
      have hl : raw34183step1Labels = raw34183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34183step0 raw34183step0Labels permutation32 permutation3
    mixedMoment B raw34183step1 raw34183step1Labels = mixedMoment B raw34183step2 raw34183step2Labels := by
      have ha : raw34183step2 = raw34183step1 := by apply Matrix.ext; unfold raw34183step2 raw34183step1; decide +kernel
      have hl : raw34183step1Labels = labelEmbedding6 ∘ raw34183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34183step1 raw34183step1Labels raw34183step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw34184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw34184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw34184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw34184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34184step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34184 raw34184Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw34184 raw34184Labels = mixedMoment B raw34184step0 raw34184step0Labels := by
      have hz : ∀ j, raw34184 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34184step0 = (fun i j => raw34184 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34184step0 raw34184; decide +kernel
      have hl : raw34184step0Labels = raw34184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34184 raw34184Labels permutation520 hz
    mixedMoment B raw34184step0 raw34184step0Labels = mixedMoment B raw34184step1 raw34184step1Labels := by
      have hz : ∀ j, raw34184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34184step1 = (fun i j => raw34184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34184step1 raw34184step0; decide +kernel
      have hl : raw34184step1Labels = raw34184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34184step0 raw34184step0Labels permutation80 hz
    mixedMoment B raw34184step1 raw34184step1Labels = mixedMoment B raw34184step2 raw34184step2Labels := by
      have ha : raw34184step2 = (fun i j => raw34184step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34184step2 raw34184step1; decide +kernel
      have hl : raw34184step2Labels = raw34184step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34184step1 raw34184step1Labels permutation8 permutation3
    mixedMoment B raw34184step2 raw34184step2Labels = mixedMoment B raw34184step3 raw34184step3Labels := by
      have ha : raw34184step3 = raw34184step2 := by apply Matrix.ext; unfold raw34184step3 raw34184step2; decide +kernel
      have hl : raw34184step2Labels = labelEmbedding6 ∘ raw34184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34184step2 raw34184step2Labels raw34184step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw34185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34185 raw34185Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw34185 raw34185Labels = mixedMoment B raw34185step0 raw34185step0Labels := by
      have hz : ∀ j, raw34185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34185step0 = (fun i j => raw34185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34185step0 raw34185; decide +kernel
      have hl : raw34185step0Labels = raw34185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34185 raw34185Labels permutation346 hz
    mixedMoment B raw34185step0 raw34185step0Labels = mixedMoment B raw34185step1 raw34185step1Labels := by
      have ha : raw34185step1 = (fun i j => raw34185step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34185step1 raw34185step0; decide +kernel
      have hl : raw34185step1Labels = raw34185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34185step0 raw34185step0Labels permutation37 permutation4
    mixedMoment B raw34185step1 raw34185step1Labels = mixedMoment B raw34185step2 raw34185step2Labels := by
      have ha : raw34185step2 = -raw34185step1 := by apply Matrix.ext; change ∀ i j, raw34185step2 i j = -(raw34185step1 i j); unfold raw34185step2 raw34185step1; decide +kernel
      have hl : raw34185step2Labels = raw34185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34185step2 raw34185step2Labels = mixedMoment B raw34185step3 raw34185step3Labels := by
      have ha : raw34185step3 = raw34185step2 := by apply Matrix.ext; unfold raw34185step3 raw34185step2; decide +kernel
      have hl : raw34185step2Labels = labelEmbedding7 ∘ raw34185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34185step2 raw34185step2Labels raw34185step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw34186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34186 raw34186Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw34186 raw34186Labels = mixedMoment B raw34186step0 raw34186step0Labels := by
      have hz : ∀ j, raw34186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34186step0 = (fun i j => raw34186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34186step0 raw34186; decide +kernel
      have hl : raw34186step0Labels = raw34186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34186 raw34186Labels permutation346 hz
    mixedMoment B raw34186step0 raw34186step0Labels = mixedMoment B raw34186step1 raw34186step1Labels := by
      have ha : raw34186step1 = (fun i j => raw34186step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34186step1 raw34186step0; decide +kernel
      have hl : raw34186step1Labels = raw34186step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34186step0 raw34186step0Labels permutation37 permutation4
    mixedMoment B raw34186step1 raw34186step1Labels = mixedMoment B raw34186step2 raw34186step2Labels := by
      have ha : raw34186step2 = -raw34186step1 := by apply Matrix.ext; change ∀ i j, raw34186step2 i j = -(raw34186step1 i j); unfold raw34186step2 raw34186step1; decide +kernel
      have hl : raw34186step2Labels = raw34186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34186step2 raw34186step2Labels = mixedMoment B raw34186step3 raw34186step3Labels := by
      have ha : raw34186step3 = raw34186step2 := by apply Matrix.ext; unfold raw34186step3 raw34186step2; decide +kernel
      have hl : raw34186step2Labels = labelEmbedding7 ∘ raw34186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34186step2 raw34186step2Labels raw34186step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw34187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw34187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw34187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw34187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34187 raw34187Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw34187 raw34187Labels = mixedMoment B raw34187step0 raw34187step0Labels := by
      have ha : raw34187step0 = (fun i j => raw34187 (permutation181 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34187step0 raw34187; decide +kernel
      have hl : raw34187step0Labels = raw34187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34187 raw34187Labels permutation181 permutation4
    mixedMoment B raw34187step0 raw34187step0Labels = mixedMoment B raw34187step1 raw34187step1Labels := by
      have ha : raw34187step1 = -raw34187step0 := by apply Matrix.ext; change ∀ i j, raw34187step1 i j = -(raw34187step0 i j); unfold raw34187step1 raw34187step0; decide +kernel
      have hl : raw34187step1Labels = raw34187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34187step1 raw34187step1Labels = mixedMoment B raw34187step2 raw34187step2Labels := by
      have ha : raw34187step2 = raw34187step1 := by apply Matrix.ext; unfold raw34187step2 raw34187step1; decide +kernel
      have hl : raw34187step1Labels = labelEmbedding7 ∘ raw34187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34187step1 raw34187step1Labels raw34187step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

def raw34188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34188 raw34188Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw34188 raw34188Labels = mixedMoment B raw34188step0 raw34188step0Labels := by
      have hz : ∀ j, raw34188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34188step0 = (fun i j => raw34188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34188step0 raw34188; decide +kernel
      have hl : raw34188step0Labels = raw34188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34188 raw34188Labels permutation346 hz
    mixedMoment B raw34188step0 raw34188step0Labels = mixedMoment B raw34188step1 raw34188step1Labels := by
      have ha : raw34188step1 = (fun i j => raw34188step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34188step1 raw34188step0; decide +kernel
      have hl : raw34188step1Labels = raw34188step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34188step0 raw34188step0Labels permutation34 permutation6
    mixedMoment B raw34188step1 raw34188step1Labels = mixedMoment B raw34188step2 raw34188step2Labels := by
      have ha : raw34188step2 = raw34188step1 := by apply Matrix.ext; unfold raw34188step2 raw34188step1; decide +kernel
      have hl : raw34188step1Labels = labelEmbedding9 ∘ raw34188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34188step1 raw34188step1Labels raw34188step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw34189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw34189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34189 raw34189Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw34189 raw34189Labels = mixedMoment B raw34189step0 raw34189step0Labels := by
      have hz : ∀ j, raw34189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34189step0 = (fun i j => raw34189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34189step0 raw34189; decide +kernel
      have hl : raw34189step0Labels = raw34189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34189 raw34189Labels permutation346 hz
    mixedMoment B raw34189step0 raw34189step0Labels = mixedMoment B raw34189step1 raw34189step1Labels := by
      have ha : raw34189step1 = (fun i j => raw34189step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34189step1 raw34189step0; decide +kernel
      have hl : raw34189step1Labels = raw34189step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34189step0 raw34189step0Labels permutation34 permutation6
    mixedMoment B raw34189step1 raw34189step1Labels = mixedMoment B raw34189step2 raw34189step2Labels := by
      have ha : raw34189step2 = raw34189step1 := by apply Matrix.ext; unfold raw34189step2 raw34189step1; decide +kernel
      have hl : raw34189step1Labels = labelEmbedding9 ∘ raw34189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34189step1 raw34189step1Labels raw34189step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw34190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34190step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34190 raw34190Labels = mixedMoment B node4412 node4412Labels := by
  calc
    mixedMoment B raw34190 raw34190Labels = mixedMoment B raw34190step0 raw34190step0Labels := by
      have hz : ∀ j, raw34190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34190step0 = (fun i j => raw34190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34190step0 raw34190; decide +kernel
      have hl : raw34190step0Labels = raw34190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34190 raw34190Labels permutation346 hz
    mixedMoment B raw34190step0 raw34190step0Labels = mixedMoment B raw34190step1 raw34190step1Labels := by
      have ha : raw34190step1 = (fun i j => raw34190step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34190step1 raw34190step0; decide +kernel
      have hl : raw34190step1Labels = raw34190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34190step0 raw34190step0Labels permutation36 permutation4
    mixedMoment B raw34190step1 raw34190step1Labels = mixedMoment B raw34190step2 raw34190step2Labels := by
      have ha : raw34190step2 = -raw34190step1 := by apply Matrix.ext; change ∀ i j, raw34190step2 i j = -(raw34190step1 i j); unfold raw34190step2 raw34190step1; decide +kernel
      have hl : raw34190step2Labels = raw34190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34190step2 raw34190step2Labels = mixedMoment B raw34190step3 raw34190step3Labels := by
      have ha : raw34190step3 = raw34190step2 := by apply Matrix.ext; unfold raw34190step3 raw34190step2; decide +kernel
      have hl : raw34190step2Labels = labelEmbedding7 ∘ raw34190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34190step2 raw34190step2Labels raw34190step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4412 node4412Labels := by rfl

def raw34191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34191 raw34191Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw34191 raw34191Labels = mixedMoment B raw34191step0 raw34191step0Labels := by
      have hz : ∀ j, raw34191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34191step0 = (fun i j => raw34191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34191step0 raw34191; decide +kernel
      have hl : raw34191step0Labels = raw34191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34191 raw34191Labels permutation346 hz
    mixedMoment B raw34191step0 raw34191step0Labels = mixedMoment B raw34191step1 raw34191step1Labels := by
      have ha : raw34191step1 = (fun i j => raw34191step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34191step1 raw34191step0; decide +kernel
      have hl : raw34191step1Labels = raw34191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34191step0 raw34191step0Labels permutation36 permutation4
    mixedMoment B raw34191step1 raw34191step1Labels = mixedMoment B raw34191step2 raw34191step2Labels := by
      have ha : raw34191step2 = -raw34191step1 := by apply Matrix.ext; change ∀ i j, raw34191step2 i j = -(raw34191step1 i j); unfold raw34191step2 raw34191step1; decide +kernel
      have hl : raw34191step2Labels = raw34191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34191step2 raw34191step2Labels = mixedMoment B raw34191step3 raw34191step3Labels := by
      have ha : raw34191step3 = raw34191step2 := by apply Matrix.ext; unfold raw34191step3 raw34191step2; decide +kernel
      have hl : raw34191step2Labels = labelEmbedding7 ∘ raw34191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34191step2 raw34191step2Labels raw34191step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw34192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw34192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw34192step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34192 raw34192Labels = mixedMoment B node4785 node4785Labels := by
  calc
    mixedMoment B raw34192 raw34192Labels = mixedMoment B raw34192step0 raw34192step0Labels := by
      have ha : raw34192step0 = (fun i j => raw34192 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34192step0 raw34192; decide +kernel
      have hl : raw34192step0Labels = raw34192Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34192 raw34192Labels permutation180 permutation4
    mixedMoment B raw34192step0 raw34192step0Labels = mixedMoment B raw34192step1 raw34192step1Labels := by
      have ha : raw34192step1 = -raw34192step0 := by apply Matrix.ext; change ∀ i j, raw34192step1 i j = -(raw34192step0 i j); unfold raw34192step1 raw34192step0; decide +kernel
      have hl : raw34192step1Labels = raw34192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34192step1 raw34192step1Labels = mixedMoment B raw34192step2 raw34192step2Labels := by
      have ha : raw34192step2 = raw34192step1 := by apply Matrix.ext; unfold raw34192step2 raw34192step1; decide +kernel
      have hl : raw34192step1Labels = labelEmbedding7 ∘ raw34192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34192step1 raw34192step1Labels raw34192step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4785 node4785Labels := by rfl

def raw34193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw34193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw34193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34193 raw34193Labels = mixedMoment B node4842 node4842Labels := by
  calc
    mixedMoment B raw34193 raw34193Labels = mixedMoment B raw34193step0 raw34193step0Labels := by
      have hz : ∀ j, raw34193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34193step0 = (fun i j => raw34193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34193step0 raw34193; decide +kernel
      have hl : raw34193step0Labels = raw34193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34193 raw34193Labels permutation346 hz
    mixedMoment B raw34193step0 raw34193step0Labels = mixedMoment B raw34193step1 raw34193step1Labels := by
      have ha : raw34193step1 = (fun i j => raw34193step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34193step1 raw34193step0; decide +kernel
      have hl : raw34193step1Labels = raw34193step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34193step0 raw34193step0Labels permutation32 permutation6
    mixedMoment B raw34193step1 raw34193step1Labels = mixedMoment B raw34193step2 raw34193step2Labels := by
      have ha : raw34193step2 = raw34193step1 := by apply Matrix.ext; unfold raw34193step2 raw34193step1; decide +kernel
      have hl : raw34193step1Labels = labelEmbedding9 ∘ raw34193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34193step1 raw34193step1Labels raw34193step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4842 node4842Labels := by rfl

def raw34194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34194step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34194 raw34194Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw34194 raw34194Labels = mixedMoment B raw34194step0 raw34194step0Labels := by
      have hz : ∀ j, raw34194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34194step0 = (fun i j => raw34194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34194step0 raw34194; decide +kernel
      have hl : raw34194step0Labels = raw34194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34194 raw34194Labels permutation346 hz
    mixedMoment B raw34194step0 raw34194step0Labels = mixedMoment B raw34194step1 raw34194step1Labels := by
      have ha : raw34194step1 = (fun i j => raw34194step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34194step1 raw34194step0; decide +kernel
      have hl : raw34194step1Labels = raw34194step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34194step0 raw34194step0Labels permutation35 permutation4
    mixedMoment B raw34194step1 raw34194step1Labels = mixedMoment B raw34194step2 raw34194step2Labels := by
      have ha : raw34194step2 = -raw34194step1 := by apply Matrix.ext; change ∀ i j, raw34194step2 i j = -(raw34194step1 i j); unfold raw34194step2 raw34194step1; decide +kernel
      have hl : raw34194step2Labels = raw34194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34194step2 raw34194step2Labels = mixedMoment B raw34194step3 raw34194step3Labels := by
      have ha : raw34194step3 = raw34194step2 := by apply Matrix.ext; unfold raw34194step3 raw34194step2; decide +kernel
      have hl : raw34194step2Labels = labelEmbedding7 ∘ raw34194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34194step2 raw34194step2Labels raw34194step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw34195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34195step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34195 raw34195Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw34195 raw34195Labels = mixedMoment B raw34195step0 raw34195step0Labels := by
      have hz : ∀ j, raw34195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34195step0 = (fun i j => raw34195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34195step0 raw34195; decide +kernel
      have hl : raw34195step0Labels = raw34195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34195 raw34195Labels permutation346 hz
    mixedMoment B raw34195step0 raw34195step0Labels = mixedMoment B raw34195step1 raw34195step1Labels := by
      have ha : raw34195step1 = (fun i j => raw34195step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34195step1 raw34195step0; decide +kernel
      have hl : raw34195step1Labels = raw34195step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34195step0 raw34195step0Labels permutation35 permutation4
    mixedMoment B raw34195step1 raw34195step1Labels = mixedMoment B raw34195step2 raw34195step2Labels := by
      have ha : raw34195step2 = -raw34195step1 := by apply Matrix.ext; change ∀ i j, raw34195step2 i j = -(raw34195step1 i j); unfold raw34195step2 raw34195step1; decide +kernel
      have hl : raw34195step2Labels = raw34195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34195step2 raw34195step2Labels = mixedMoment B raw34195step3 raw34195step3Labels := by
      have ha : raw34195step3 = raw34195step2 := by apply Matrix.ext; unfold raw34195step3 raw34195step2; decide +kernel
      have hl : raw34195step2Labels = labelEmbedding7 ∘ raw34195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34195step2 raw34195step2Labels raw34195step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4752 node4752Labels := by rfl

def raw34196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34196step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34196step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34196 raw34196Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw34196 raw34196Labels = mixedMoment B raw34196step0 raw34196step0Labels := by
      have hz : ∀ j, raw34196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34196step0 = (fun i j => raw34196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34196step0 raw34196; decide +kernel
      have hl : raw34196step0Labels = raw34196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34196 raw34196Labels permutation346 hz
    mixedMoment B raw34196step0 raw34196step0Labels = mixedMoment B raw34196step1 raw34196step1Labels := by
      have ha : raw34196step1 = (fun i j => raw34196step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34196step1 raw34196step0; decide +kernel
      have hl : raw34196step1Labels = raw34196step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34196step0 raw34196step0Labels permutation35 permutation7
    mixedMoment B raw34196step1 raw34196step1Labels = mixedMoment B raw34196step2 raw34196step2Labels := by
      have ha : raw34196step2 = -raw34196step1 := by apply Matrix.ext; change ∀ i j, raw34196step2 i j = -(raw34196step1 i j); unfold raw34196step2 raw34196step1; decide +kernel
      have hl : raw34196step2Labels = raw34196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34196step2 raw34196step2Labels = mixedMoment B raw34196step3 raw34196step3Labels := by
      have ha : raw34196step3 = raw34196step2 := by apply Matrix.ext; unfold raw34196step3 raw34196step2; decide +kernel
      have hl : raw34196step2Labels = labelEmbedding10 ∘ raw34196step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34196step2 raw34196step2Labels raw34196step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw34197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34197step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34197 raw34197Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw34197 raw34197Labels = mixedMoment B raw34197step0 raw34197step0Labels := by
      have ha : raw34197step0 = (fun i j => raw34197 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34197step0 raw34197; decide +kernel
      have hl : raw34197step0Labels = raw34197Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34197 raw34197Labels permutation155 permutation7
    mixedMoment B raw34197step0 raw34197step0Labels = mixedMoment B raw34197step1 raw34197step1Labels := by
      have ha : raw34197step1 = -raw34197step0 := by apply Matrix.ext; change ∀ i j, raw34197step1 i j = -(raw34197step0 i j); unfold raw34197step1 raw34197step0; decide +kernel
      have hl : raw34197step1Labels = raw34197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34197step1 raw34197step1Labels = mixedMoment B raw34197step2 raw34197step2Labels := by
      have ha : raw34197step2 = raw34197step1 := by apply Matrix.ext; unfold raw34197step2 raw34197step1; decide +kernel
      have hl : raw34197step1Labels = labelEmbedding10 ∘ raw34197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34197step1 raw34197step1Labels raw34197step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw34198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34198step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34198 raw34198Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw34198 raw34198Labels = mixedMoment B raw34198step0 raw34198step0Labels := by
      have hz : ∀ j, raw34198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34198step0 = (fun i j => raw34198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34198step0 raw34198; decide +kernel
      have hl : raw34198step0Labels = raw34198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34198 raw34198Labels permutation346 hz
    mixedMoment B raw34198step0 raw34198step0Labels = mixedMoment B raw34198step1 raw34198step1Labels := by
      have ha : raw34198step1 = (fun i j => raw34198step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34198step1 raw34198step0; decide +kernel
      have hl : raw34198step1Labels = raw34198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34198step0 raw34198step0Labels permutation35 permutation7
    mixedMoment B raw34198step1 raw34198step1Labels = mixedMoment B raw34198step2 raw34198step2Labels := by
      have ha : raw34198step2 = -raw34198step1 := by apply Matrix.ext; change ∀ i j, raw34198step2 i j = -(raw34198step1 i j); unfold raw34198step2 raw34198step1; decide +kernel
      have hl : raw34198step2Labels = raw34198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34198step2 raw34198step2Labels = mixedMoment B raw34198step3 raw34198step3Labels := by
      have ha : raw34198step3 = raw34198step2 := by apply Matrix.ext; unfold raw34198step3 raw34198step2; decide +kernel
      have hl : raw34198step2Labels = labelEmbedding10 ∘ raw34198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34198step2 raw34198step2Labels raw34198step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw34199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34199step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34199step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34199step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34199 raw34199Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw34199 raw34199Labels = mixedMoment B raw34199step0 raw34199step0Labels := by
      have hz : ∀ j, raw34199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34199step0 = (fun i j => raw34199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34199step0 raw34199; decide +kernel
      have hl : raw34199step0Labels = raw34199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34199 raw34199Labels permutation520 hz
    mixedMoment B raw34199step0 raw34199step0Labels = mixedMoment B raw34199step1 raw34199step1Labels := by
      have hz : ∀ j, raw34199step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34199step1 = (fun i j => raw34199step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34199step1 raw34199step0; decide +kernel
      have hl : raw34199step1Labels = raw34199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34199step0 raw34199step0Labels permutation80 hz
    mixedMoment B raw34199step1 raw34199step1Labels = mixedMoment B raw34199step2 raw34199step2Labels := by
      have ha : raw34199step2 = (fun i j => raw34199step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34199step2 raw34199step1; decide +kernel
      have hl : raw34199step2Labels = raw34199step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34199step1 raw34199step1Labels permutation9 permutation7
    mixedMoment B raw34199step2 raw34199step2Labels = mixedMoment B raw34199step3 raw34199step3Labels := by
      have ha : raw34199step3 = -raw34199step2 := by apply Matrix.ext; change ∀ i j, raw34199step3 i j = -(raw34199step2 i j); unfold raw34199step3 raw34199step2; decide +kernel
      have hl : raw34199step3Labels = raw34199step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34199step3 raw34199step3Labels = mixedMoment B raw34199step4 raw34199step4Labels := by
      have ha : raw34199step4 = raw34199step3 := by apply Matrix.ext; unfold raw34199step4 raw34199step3; decide +kernel
      have hl : raw34199step3Labels = labelEmbedding10 ∘ raw34199step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34199step3 raw34199step3Labels raw34199step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw34200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34200step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34200 raw34200Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34200 raw34200Labels = mixedMoment B raw34200step0 raw34200step0Labels := by
      have hz : ∀ j, raw34200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34200step0 = (fun i j => raw34200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34200step0 raw34200; decide +kernel
      have hl : raw34200step0Labels = raw34200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34200 raw34200Labels permutation346 hz
    mixedMoment B raw34200step0 raw34200step0Labels = mixedMoment B raw34200step1 raw34200step1Labels := by
      have ha : raw34200step1 = (fun i j => raw34200step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34200step1 raw34200step0; decide +kernel
      have hl : raw34200step1Labels = raw34200step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34200step0 raw34200step0Labels permutation35 permutation7
    mixedMoment B raw34200step1 raw34200step1Labels = mixedMoment B raw34200step2 raw34200step2Labels := by
      have ha : raw34200step2 = -raw34200step1 := by apply Matrix.ext; change ∀ i j, raw34200step2 i j = -(raw34200step1 i j); unfold raw34200step2 raw34200step1; decide +kernel
      have hl : raw34200step2Labels = raw34200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34200step2 raw34200step2Labels = mixedMoment B raw34200step3 raw34200step3Labels := by
      have ha : raw34200step3 = raw34200step2 := by apply Matrix.ext; unfold raw34200step3 raw34200step2; decide +kernel
      have hl : raw34200step2Labels = labelEmbedding10 ∘ raw34200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34200step2 raw34200step2Labels raw34200step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw34201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34201 raw34201Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw34201 raw34201Labels = mixedMoment B raw34201step0 raw34201step0Labels := by
      have hz : ∀ j, raw34201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34201step0 = (fun i j => raw34201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34201step0 raw34201; decide +kernel
      have hl : raw34201step0Labels = raw34201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34201 raw34201Labels permutation346 hz
    mixedMoment B raw34201step0 raw34201step0Labels = mixedMoment B raw34201step1 raw34201step1Labels := by
      have hz : ∀ j, raw34201step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34201step1 = (fun i j => raw34201step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34201step1 raw34201step0; decide +kernel
      have hl : raw34201step1Labels = raw34201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34201step0 raw34201step0Labels permutation56 hz
    mixedMoment B raw34201step1 raw34201step1Labels = mixedMoment B raw34201step2 raw34201step2Labels := by
      have ha : raw34201step2 = (fun i j => raw34201step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34201step2 raw34201step1; decide +kernel
      have hl : raw34201step2Labels = raw34201step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34201step1 raw34201step1Labels permutation10 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw34202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34202 raw34202Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw34202 raw34202Labels = mixedMoment B raw34202step0 raw34202step0Labels := by
      have ha : raw34202step0 = (fun i j => raw34202 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34202step0 raw34202; decide +kernel
      have hl : raw34202step0Labels = raw34202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34202 raw34202Labels permutation154 permutation2
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw34203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34203 raw34203Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw34203 raw34203Labels = mixedMoment B raw34203step0 raw34203step0Labels := by
      have ha : raw34203step0 = (fun i j => raw34203 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34203step0 raw34203; decide +kernel
      have hl : raw34203step0Labels = raw34203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34203 raw34203Labels permutation158 permutation2
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw34204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34204 raw34204Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34204 raw34204Labels = mixedMoment B raw34204step0 raw34204step0Labels := by
      have hz : ∀ j, raw34204 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34204step0 = (fun i j => raw34204 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34204step0 raw34204; decide +kernel
      have hl : raw34204step0Labels = raw34204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34204 raw34204Labels permutation520 hz
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34205 raw34205Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34205 raw34205Labels = mixedMoment B raw34205step0 raw34205step0Labels := by
      have ha : raw34205step0 = (fun i j => raw34205 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34205step0 raw34205; decide +kernel
      have hl : raw34205step0Labels = raw34205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34205 raw34205Labels permutation155 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34206 raw34206Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw34206 raw34206Labels = mixedMoment B raw34206step0 raw34206step0Labels := by
      have hz : ∀ j, raw34206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34206step0 = (fun i j => raw34206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34206step0 raw34206; decide +kernel
      have hl : raw34206step0Labels = raw34206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34206 raw34206Labels permutation346 hz
    mixedMoment B raw34206step0 raw34206step0Labels = mixedMoment B raw34206step1 raw34206step1Labels := by
      have ha : raw34206step1 = (fun i j => raw34206step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34206step1 raw34206step0; decide +kernel
      have hl : raw34206step1Labels = raw34206step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34206step0 raw34206step0Labels permutation35 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw34207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34207 raw34207Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34207 raw34207Labels = mixedMoment B raw34207step0 raw34207step0Labels := by
      have ha : raw34207step0 = (fun i j => raw34207 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34207step0 raw34207; decide +kernel
      have hl : raw34207step0Labels = raw34207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34207 raw34207Labels permutation155 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw34208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34208 raw34208Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw34208 raw34208Labels = mixedMoment B raw34208step0 raw34208step0Labels := by
      have hz : ∀ j, raw34208 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34208step0 = (fun i j => raw34208 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34208step0 raw34208; decide +kernel
      have hl : raw34208step0Labels = raw34208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34208 raw34208Labels permutation520 hz
    mixedMoment B raw34208step0 raw34208step0Labels = mixedMoment B raw34208step1 raw34208step1Labels := by
      have hz : ∀ j, raw34208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34208step1 = (fun i j => raw34208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34208step1 raw34208step0; decide +kernel
      have hl : raw34208step1Labels = raw34208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34208step0 raw34208step0Labels permutation80 hz
    mixedMoment B raw34208step1 raw34208step1Labels = mixedMoment B raw34208step2 raw34208step2Labels := by
      have ha : raw34208step2 = (fun i j => raw34208step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34208step2 raw34208step1; decide +kernel
      have hl : raw34208step2Labels = raw34208step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34208step1 raw34208step1Labels permutation9 permutation2
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw34209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34209 raw34209Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34209 raw34209Labels = mixedMoment B raw34209step0 raw34209step0Labels := by
      have hz : ∀ j, raw34209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34209step0 = (fun i j => raw34209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34209step0 raw34209; decide +kernel
      have hl : raw34209step0Labels = raw34209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34209 raw34209Labels permutation346 hz
    mixedMoment B raw34209step0 raw34209step0Labels = mixedMoment B raw34209step1 raw34209step1Labels := by
      have ha : raw34209step1 = (fun i j => raw34209step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34209step1 raw34209step0; decide +kernel
      have hl : raw34209step1Labels = raw34209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34209step0 raw34209step0Labels permutation35 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34210 raw34210Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw34210 raw34210Labels = mixedMoment B raw34210step0 raw34210step0Labels := by
      have hz : ∀ j, raw34210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34210step0 = (fun i j => raw34210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34210step0 raw34210; decide +kernel
      have hl : raw34210step0Labels = raw34210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34210 raw34210Labels permutation346 hz
    _ = mixedMoment B node4690 node4690Labels := by rfl

def raw34211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34211 raw34211Labels = mixedMoment B node4768 node4768Labels := by
  calc
    _ = mixedMoment B node4768 node4768Labels := by rfl

def raw34212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34212 raw34212Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw34212 raw34212Labels = mixedMoment B raw34212step0 raw34212step0Labels := by
      have hz : ∀ j, raw34212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34212step0 = (fun i j => raw34212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34212step0 raw34212; decide +kernel
      have hl : raw34212step0Labels = raw34212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34212 raw34212Labels permutation346 hz
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw34213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34213 raw34213Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34213 raw34213Labels = mixedMoment B raw34213step0 raw34213step0Labels := by
      have hz : ∀ j, raw34213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34213step0 = (fun i j => raw34213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34213step0 raw34213; decide +kernel
      have hl : raw34213step0Labels = raw34213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34213 raw34213Labels permutation346 hz
    mixedMoment B raw34213step0 raw34213step0Labels = mixedMoment B raw34213step1 raw34213step1Labels := by
      have ha : raw34213step1 = (fun i j => raw34213step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34213step1 raw34213step0; decide +kernel
      have hl : raw34213step1Labels = raw34213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34213step0 raw34213step0Labels permutation36 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw34214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34214 raw34214Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw34214 raw34214Labels = mixedMoment B raw34214step0 raw34214step0Labels := by
      have hz : ∀ j, raw34214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34214step0 = (fun i j => raw34214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34214step0 raw34214; decide +kernel
      have hl : raw34214step0Labels = raw34214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34214 raw34214Labels permutation346 hz
    mixedMoment B raw34214step0 raw34214step0Labels = mixedMoment B raw34214step1 raw34214step1Labels := by
      have ha : raw34214step1 = (fun i j => raw34214step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34214step1 raw34214step0; decide +kernel
      have hl : raw34214step1Labels = raw34214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34214step0 raw34214step0Labels permutation34 permutation2
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw34215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34215 raw34215Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw34215 raw34215Labels = mixedMoment B raw34215step0 raw34215step0Labels := by
      have ha : raw34215step0 = (fun i j => raw34215 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34215step0 raw34215; decide +kernel
      have hl : raw34215step0Labels = raw34215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34215 raw34215Labels permutation154 permutation2
    _ = mixedMoment B node4761 node4761Labels := by rfl

def raw34216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34216 raw34216Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw34216 raw34216Labels = mixedMoment B raw34216step0 raw34216step0Labels := by
      have hz : ∀ j, raw34216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34216step0 = (fun i j => raw34216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34216step0 raw34216; decide +kernel
      have hl : raw34216step0Labels = raw34216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34216 raw34216Labels permutation346 hz
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw34217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34217 raw34217Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw34217 raw34217Labels = mixedMoment B raw34217step0 raw34217step0Labels := by
      have hz : ∀ j, raw34217 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34217step0 = (fun i j => raw34217 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34217step0 raw34217; decide +kernel
      have hl : raw34217step0Labels = raw34217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34217 raw34217Labels permutation520 hz
    mixedMoment B raw34217step0 raw34217step0Labels = mixedMoment B raw34217step1 raw34217step1Labels := by
      have hz : ∀ j, raw34217step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34217step1 = (fun i j => raw34217step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34217step1 raw34217step0; decide +kernel
      have hl : raw34217step1Labels = raw34217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34217step0 raw34217step0Labels permutation80 hz
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw34218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34218 raw34218Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw34218 raw34218Labels = mixedMoment B raw34218step0 raw34218step0Labels := by
      have hz : ∀ j, raw34218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34218step0 = (fun i j => raw34218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34218step0 raw34218; decide +kernel
      have hl : raw34218step0Labels = raw34218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34218 raw34218Labels permutation346 hz
    mixedMoment B raw34218step0 raw34218step0Labels = mixedMoment B raw34218step1 raw34218step1Labels := by
      have ha : raw34218step1 = (fun i j => raw34218step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34218step1 raw34218step0; decide +kernel
      have hl : raw34218step1Labels = raw34218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34218step0 raw34218step0Labels permutation35 permutation7
    mixedMoment B raw34218step1 raw34218step1Labels = mixedMoment B raw34218step2 raw34218step2Labels := by
      have ha : raw34218step2 = -raw34218step1 := by apply Matrix.ext; change ∀ i j, raw34218step2 i j = -(raw34218step1 i j); unfold raw34218step2 raw34218step1; decide +kernel
      have hl : raw34218step2Labels = raw34218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34218step2 raw34218step2Labels = mixedMoment B raw34218step3 raw34218step3Labels := by
      have ha : raw34218step3 = raw34218step2 := by apply Matrix.ext; unfold raw34218step3 raw34218step2; decide +kernel
      have hl : raw34218step2Labels = labelEmbedding1 ∘ raw34218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34218step2 raw34218step2Labels raw34218step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw34219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34219 raw34219Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw34219 raw34219Labels = mixedMoment B raw34219step0 raw34219step0Labels := by
      have ha : raw34219step0 = (fun i j => raw34219 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34219step0 raw34219; decide +kernel
      have hl : raw34219step0Labels = raw34219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34219 raw34219Labels permutation155 permutation7
    mixedMoment B raw34219step0 raw34219step0Labels = mixedMoment B raw34219step1 raw34219step1Labels := by
      have ha : raw34219step1 = -raw34219step0 := by apply Matrix.ext; change ∀ i j, raw34219step1 i j = -(raw34219step0 i j); unfold raw34219step1 raw34219step0; decide +kernel
      have hl : raw34219step1Labels = raw34219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34219step1 raw34219step1Labels = mixedMoment B raw34219step2 raw34219step2Labels := by
      have ha : raw34219step2 = raw34219step1 := by apply Matrix.ext; unfold raw34219step2 raw34219step1; decide +kernel
      have hl : raw34219step1Labels = labelEmbedding1 ∘ raw34219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34219step1 raw34219step1Labels raw34219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw34220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34220 raw34220Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw34220 raw34220Labels = mixedMoment B raw34220step0 raw34220step0Labels := by
      have hz : ∀ j, raw34220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34220step0 = (fun i j => raw34220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34220step0 raw34220; decide +kernel
      have hl : raw34220step0Labels = raw34220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34220 raw34220Labels permutation346 hz
    mixedMoment B raw34220step0 raw34220step0Labels = mixedMoment B raw34220step1 raw34220step1Labels := by
      have ha : raw34220step1 = (fun i j => raw34220step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34220step1 raw34220step0; decide +kernel
      have hl : raw34220step1Labels = raw34220step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34220step0 raw34220step0Labels permutation35 permutation7
    mixedMoment B raw34220step1 raw34220step1Labels = mixedMoment B raw34220step2 raw34220step2Labels := by
      have ha : raw34220step2 = -raw34220step1 := by apply Matrix.ext; change ∀ i j, raw34220step2 i j = -(raw34220step1 i j); unfold raw34220step2 raw34220step1; decide +kernel
      have hl : raw34220step2Labels = raw34220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34220step2 raw34220step2Labels = mixedMoment B raw34220step3 raw34220step3Labels := by
      have ha : raw34220step3 = raw34220step2 := by apply Matrix.ext; unfold raw34220step3 raw34220step2; decide +kernel
      have hl : raw34220step2Labels = labelEmbedding1 ∘ raw34220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34220step2 raw34220step2Labels raw34220step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw34221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34221step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34221step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34221step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34221 raw34221Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw34221 raw34221Labels = mixedMoment B raw34221step0 raw34221step0Labels := by
      have hz : ∀ j, raw34221 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34221step0 = (fun i j => raw34221 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34221step0 raw34221; decide +kernel
      have hl : raw34221step0Labels = raw34221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34221 raw34221Labels permutation520 hz
    mixedMoment B raw34221step0 raw34221step0Labels = mixedMoment B raw34221step1 raw34221step1Labels := by
      have hz : ∀ j, raw34221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34221step1 = (fun i j => raw34221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34221step1 raw34221step0; decide +kernel
      have hl : raw34221step1Labels = raw34221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34221step0 raw34221step0Labels permutation80 hz
    mixedMoment B raw34221step1 raw34221step1Labels = mixedMoment B raw34221step2 raw34221step2Labels := by
      have ha : raw34221step2 = (fun i j => raw34221step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34221step2 raw34221step1; decide +kernel
      have hl : raw34221step2Labels = raw34221step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34221step1 raw34221step1Labels permutation9 permutation7
    mixedMoment B raw34221step2 raw34221step2Labels = mixedMoment B raw34221step3 raw34221step3Labels := by
      have ha : raw34221step3 = -raw34221step2 := by apply Matrix.ext; change ∀ i j, raw34221step3 i j = -(raw34221step2 i j); unfold raw34221step3 raw34221step2; decide +kernel
      have hl : raw34221step3Labels = raw34221step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34221step3 raw34221step3Labels = mixedMoment B raw34221step4 raw34221step4Labels := by
      have ha : raw34221step4 = raw34221step3 := by apply Matrix.ext; unfold raw34221step4 raw34221step3; decide +kernel
      have hl : raw34221step3Labels = labelEmbedding1 ∘ raw34221step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34221step3 raw34221step3Labels raw34221step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw34222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34222step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34222 raw34222Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34222 raw34222Labels = mixedMoment B raw34222step0 raw34222step0Labels := by
      have hz : ∀ j, raw34222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34222step0 = (fun i j => raw34222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34222step0 raw34222; decide +kernel
      have hl : raw34222step0Labels = raw34222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34222 raw34222Labels permutation346 hz
    mixedMoment B raw34222step0 raw34222step0Labels = mixedMoment B raw34222step1 raw34222step1Labels := by
      have ha : raw34222step1 = (fun i j => raw34222step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34222step1 raw34222step0; decide +kernel
      have hl : raw34222step1Labels = raw34222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34222step0 raw34222step0Labels permutation35 permutation7
    mixedMoment B raw34222step1 raw34222step1Labels = mixedMoment B raw34222step2 raw34222step2Labels := by
      have ha : raw34222step2 = -raw34222step1 := by apply Matrix.ext; change ∀ i j, raw34222step2 i j = -(raw34222step1 i j); unfold raw34222step2 raw34222step1; decide +kernel
      have hl : raw34222step2Labels = raw34222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34222step2 raw34222step2Labels = mixedMoment B raw34222step3 raw34222step3Labels := by
      have ha : raw34222step3 = raw34222step2 := by apply Matrix.ext; unfold raw34222step3 raw34222step2; decide +kernel
      have hl : raw34222step2Labels = labelEmbedding1 ∘ raw34222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34222step2 raw34222step2Labels raw34222step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw34223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34223step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34223step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34223step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34223 raw34223Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw34223 raw34223Labels = mixedMoment B raw34223step0 raw34223step0Labels := by
      have hz : ∀ j, raw34223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34223step0 = (fun i j => raw34223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34223step0 raw34223; decide +kernel
      have hl : raw34223step0Labels = raw34223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34223 raw34223Labels permutation346 hz
    mixedMoment B raw34223step0 raw34223step0Labels = mixedMoment B raw34223step1 raw34223step1Labels := by
      have hz : ∀ j, raw34223step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34223step1 = (fun i j => raw34223step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34223step1 raw34223step0; decide +kernel
      have hl : raw34223step1Labels = raw34223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34223step0 raw34223step0Labels permutation56 hz
    mixedMoment B raw34223step1 raw34223step1Labels = mixedMoment B raw34223step2 raw34223step2Labels := by
      have ha : raw34223step2 = (fun i j => raw34223step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34223step2 raw34223step1; decide +kernel
      have hl : raw34223step2Labels = raw34223step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34223step1 raw34223step1Labels permutation11 permutation7
    mixedMoment B raw34223step2 raw34223step2Labels = mixedMoment B raw34223step3 raw34223step3Labels := by
      have ha : raw34223step3 = -raw34223step2 := by apply Matrix.ext; change ∀ i j, raw34223step3 i j = -(raw34223step2 i j); unfold raw34223step3 raw34223step2; decide +kernel
      have hl : raw34223step3Labels = raw34223step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34223step3 raw34223step3Labels = mixedMoment B raw34223step4 raw34223step4Labels := by
      have ha : raw34223step4 = raw34223step3 := by apply Matrix.ext; unfold raw34223step4 raw34223step3; decide +kernel
      have hl : raw34223step3Labels = labelEmbedding1 ∘ raw34223step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34223step3 raw34223step3Labels raw34223step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw34224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34224 raw34224Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw34224 raw34224Labels = mixedMoment B raw34224step0 raw34224step0Labels := by
      have ha : raw34224step0 = (fun i j => raw34224 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34224step0 raw34224; decide +kernel
      have hl : raw34224step0Labels = raw34224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34224 raw34224Labels permutation155 permutation7
    mixedMoment B raw34224step0 raw34224step0Labels = mixedMoment B raw34224step1 raw34224step1Labels := by
      have ha : raw34224step1 = -raw34224step0 := by apply Matrix.ext; change ∀ i j, raw34224step1 i j = -(raw34224step0 i j); unfold raw34224step1 raw34224step0; decide +kernel
      have hl : raw34224step1Labels = raw34224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34224step1 raw34224step1Labels = mixedMoment B raw34224step2 raw34224step2Labels := by
      have ha : raw34224step2 = raw34224step1 := by apply Matrix.ext; unfold raw34224step2 raw34224step1; decide +kernel
      have hl : raw34224step1Labels = labelEmbedding1 ∘ raw34224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34224step1 raw34224step1Labels raw34224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw34225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34225Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34225step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34225 raw34225Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw34225 raw34225Labels = mixedMoment B raw34225step0 raw34225step0Labels := by
      have ha : raw34225step0 = (fun i j => raw34225 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34225step0 raw34225; decide +kernel
      have hl : raw34225step0Labels = raw34225Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34225 raw34225Labels permutation155 permutation7
    mixedMoment B raw34225step0 raw34225step0Labels = mixedMoment B raw34225step1 raw34225step1Labels := by
      have ha : raw34225step1 = -raw34225step0 := by apply Matrix.ext; change ∀ i j, raw34225step1 i j = -(raw34225step0 i j); unfold raw34225step1 raw34225step0; decide +kernel
      have hl : raw34225step1Labels = raw34225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34225step1 raw34225step1Labels = mixedMoment B raw34225step2 raw34225step2Labels := by
      have ha : raw34225step2 = raw34225step1 := by apply Matrix.ext; unfold raw34225step2 raw34225step1; decide +kernel
      have hl : raw34225step1Labels = labelEmbedding1 ∘ raw34225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34225step1 raw34225step1Labels raw34225step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw34226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34226step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34226step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34226 raw34226Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34226 raw34226Labels = mixedMoment B raw34226step0 raw34226step0Labels := by
      have hz : ∀ j, raw34226 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34226step0 = (fun i j => raw34226 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34226step0 raw34226; decide +kernel
      have hl : raw34226step0Labels = raw34226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34226 raw34226Labels permutation520 hz
    mixedMoment B raw34226step0 raw34226step0Labels = mixedMoment B raw34226step1 raw34226step1Labels := by
      have ha : raw34226step1 = (fun i j => raw34226step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34226step1 raw34226step0; decide +kernel
      have hl : raw34226step1Labels = raw34226step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34226step0 raw34226step0Labels permutation33 permutation7
    mixedMoment B raw34226step1 raw34226step1Labels = mixedMoment B raw34226step2 raw34226step2Labels := by
      have ha : raw34226step2 = -raw34226step1 := by apply Matrix.ext; change ∀ i j, raw34226step2 i j = -(raw34226step1 i j); unfold raw34226step2 raw34226step1; decide +kernel
      have hl : raw34226step2Labels = raw34226step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34226step2 raw34226step2Labels = mixedMoment B raw34226step3 raw34226step3Labels := by
      have ha : raw34226step3 = raw34226step2 := by apply Matrix.ext; unfold raw34226step3 raw34226step2; decide +kernel
      have hl : raw34226step2Labels = labelEmbedding1 ∘ raw34226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34226step2 raw34226step2Labels raw34226step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw34227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34227Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34227step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34227step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34227 raw34227Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34227 raw34227Labels = mixedMoment B raw34227step0 raw34227step0Labels := by
      have ha : raw34227step0 = (fun i j => raw34227 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34227step0 raw34227; decide +kernel
      have hl : raw34227step0Labels = raw34227Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34227 raw34227Labels permutation155 permutation7
    mixedMoment B raw34227step0 raw34227step0Labels = mixedMoment B raw34227step1 raw34227step1Labels := by
      have ha : raw34227step1 = -raw34227step0 := by apply Matrix.ext; change ∀ i j, raw34227step1 i j = -(raw34227step0 i j); unfold raw34227step1 raw34227step0; decide +kernel
      have hl : raw34227step1Labels = raw34227step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34227step1 raw34227step1Labels = mixedMoment B raw34227step2 raw34227step2Labels := by
      have ha : raw34227step2 = raw34227step1 := by apply Matrix.ext; unfold raw34227step2 raw34227step1; decide +kernel
      have hl : raw34227step1Labels = labelEmbedding1 ∘ raw34227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34227step1 raw34227step1Labels raw34227step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw34228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34228step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34228step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34228step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34228 raw34228Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw34228 raw34228Labels = mixedMoment B raw34228step0 raw34228step0Labels := by
      have hz : ∀ j, raw34228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34228step0 = (fun i j => raw34228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34228step0 raw34228; decide +kernel
      have hl : raw34228step0Labels = raw34228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34228 raw34228Labels permutation346 hz
    mixedMoment B raw34228step0 raw34228step0Labels = mixedMoment B raw34228step1 raw34228step1Labels := by
      have ha : raw34228step1 = (fun i j => raw34228step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34228step1 raw34228step0; decide +kernel
      have hl : raw34228step1Labels = raw34228step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34228step0 raw34228step0Labels permutation35 permutation7
    mixedMoment B raw34228step1 raw34228step1Labels = mixedMoment B raw34228step2 raw34228step2Labels := by
      have ha : raw34228step2 = -raw34228step1 := by apply Matrix.ext; change ∀ i j, raw34228step2 i j = -(raw34228step1 i j); unfold raw34228step2 raw34228step1; decide +kernel
      have hl : raw34228step2Labels = raw34228step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34228step2 raw34228step2Labels = mixedMoment B raw34228step3 raw34228step3Labels := by
      have ha : raw34228step3 = raw34228step2 := by apply Matrix.ext; unfold raw34228step3 raw34228step2; decide +kernel
      have hl : raw34228step2Labels = labelEmbedding1 ∘ raw34228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34228step2 raw34228step2Labels raw34228step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw34229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34229Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34229 raw34229Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw34229 raw34229Labels = mixedMoment B raw34229step0 raw34229step0Labels := by
      have ha : raw34229step0 = (fun i j => raw34229 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34229step0 raw34229; decide +kernel
      have hl : raw34229step0Labels = raw34229Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34229 raw34229Labels permutation155 permutation7
    mixedMoment B raw34229step0 raw34229step0Labels = mixedMoment B raw34229step1 raw34229step1Labels := by
      have ha : raw34229step1 = -raw34229step0 := by apply Matrix.ext; change ∀ i j, raw34229step1 i j = -(raw34229step0 i j); unfold raw34229step1 raw34229step0; decide +kernel
      have hl : raw34229step1Labels = raw34229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34229step1 raw34229step1Labels = mixedMoment B raw34229step2 raw34229step2Labels := by
      have ha : raw34229step2 = raw34229step1 := by apply Matrix.ext; unfold raw34229step2 raw34229step1; decide +kernel
      have hl : raw34229step1Labels = labelEmbedding1 ∘ raw34229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34229step1 raw34229step1Labels raw34229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw34230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 0, 0], ![2, -1, -1]]
def raw34230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw34230step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34230step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34230step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34230step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34230 raw34230Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw34230 raw34230Labels = mixedMoment B raw34230step0 raw34230step0Labels := by
      have hz : ∀ j, raw34230 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34230step0 = (fun i j => raw34230 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34230step0 raw34230; decide +kernel
      have hl : raw34230step0Labels = raw34230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34230 raw34230Labels permutation520 hz
    mixedMoment B raw34230step0 raw34230step0Labels = mixedMoment B raw34230step1 raw34230step1Labels := by
      have hz : ∀ j, raw34230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34230step1 = (fun i j => raw34230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34230step1 raw34230step0; decide +kernel
      have hl : raw34230step1Labels = raw34230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34230step0 raw34230step0Labels permutation80 hz
    mixedMoment B raw34230step1 raw34230step1Labels = mixedMoment B raw34230step2 raw34230step2Labels := by
      have ha : raw34230step2 = (fun i j => raw34230step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34230step2 raw34230step1; decide +kernel
      have hl : raw34230step2Labels = raw34230step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34230step1 raw34230step1Labels permutation9 permutation7
    mixedMoment B raw34230step2 raw34230step2Labels = mixedMoment B raw34230step3 raw34230step3Labels := by
      have ha : raw34230step3 = -raw34230step2 := by apply Matrix.ext; change ∀ i j, raw34230step3 i j = -(raw34230step2 i j); unfold raw34230step3 raw34230step2; decide +kernel
      have hl : raw34230step3Labels = raw34230step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34230step3 raw34230step3Labels = mixedMoment B raw34230step4 raw34230step4Labels := by
      have ha : raw34230step4 = raw34230step3 := by apply Matrix.ext; unfold raw34230step4 raw34230step3; decide +kernel
      have hl : raw34230step3Labels = labelEmbedding1 ∘ raw34230step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34230step3 raw34230step3Labels raw34230step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw34231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0], ![1, 0, -1]]
def raw34231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34231 raw34231Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34231 raw34231Labels = mixedMoment B raw34231step0 raw34231step0Labels := by
      have hz : ∀ j, raw34231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34231step0 = (fun i j => raw34231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34231step0 raw34231; decide +kernel
      have hl : raw34231step0Labels = raw34231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34231 raw34231Labels permutation346 hz
    mixedMoment B raw34231step0 raw34231step0Labels = mixedMoment B raw34231step1 raw34231step1Labels := by
      have ha : raw34231step1 = (fun i j => raw34231step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34231step1 raw34231step0; decide +kernel
      have hl : raw34231step1Labels = raw34231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34231step0 raw34231step0Labels permutation35 permutation7
    mixedMoment B raw34231step1 raw34231step1Labels = mixedMoment B raw34231step2 raw34231step2Labels := by
      have ha : raw34231step2 = -raw34231step1 := by apply Matrix.ext; change ∀ i j, raw34231step2 i j = -(raw34231step1 i j); unfold raw34231step2 raw34231step1; decide +kernel
      have hl : raw34231step2Labels = raw34231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34231step2 raw34231step2Labels = mixedMoment B raw34231step3 raw34231step3Labels := by
      have ha : raw34231step3 = raw34231step2 := by apply Matrix.ext; unfold raw34231step3 raw34231step2; decide +kernel
      have hl : raw34231step2Labels = labelEmbedding1 ∘ raw34231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34231step2 raw34231step2Labels raw34231step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34232step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34232step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34232 raw34232Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34232 raw34232Labels = mixedMoment B raw34232step0 raw34232step0Labels := by
      have hz : ∀ j, raw34232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34232step0 = (fun i j => raw34232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34232step0 raw34232; decide +kernel
      have hl : raw34232step0Labels = raw34232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34232 raw34232Labels permutation346 hz
    mixedMoment B raw34232step0 raw34232step0Labels = mixedMoment B raw34232step1 raw34232step1Labels := by
      have ha : raw34232step1 = (fun i j => raw34232step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34232step1 raw34232step0; decide +kernel
      have hl : raw34232step1Labels = raw34232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34232step0 raw34232step0Labels permutation35 permutation7
    mixedMoment B raw34232step1 raw34232step1Labels = mixedMoment B raw34232step2 raw34232step2Labels := by
      have ha : raw34232step2 = -raw34232step1 := by apply Matrix.ext; change ∀ i j, raw34232step2 i j = -(raw34232step1 i j); unfold raw34232step2 raw34232step1; decide +kernel
      have hl : raw34232step2Labels = raw34232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34232step2 raw34232step2Labels = mixedMoment B raw34232step3 raw34232step3Labels := by
      have ha : raw34232step3 = raw34232step2 := by apply Matrix.ext; unfold raw34232step3 raw34232step2; decide +kernel
      have hl : raw34232step2Labels = labelEmbedding1 ∘ raw34232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34232step2 raw34232step2Labels raw34232step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw34233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34233step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34233 raw34233Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw34233 raw34233Labels = mixedMoment B raw34233step0 raw34233step0Labels := by
      have ha : raw34233step0 = (fun i j => raw34233 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34233step0 raw34233; decide +kernel
      have hl : raw34233step0Labels = raw34233Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34233 raw34233Labels permutation155 permutation7
    mixedMoment B raw34233step0 raw34233step0Labels = mixedMoment B raw34233step1 raw34233step1Labels := by
      have ha : raw34233step1 = -raw34233step0 := by apply Matrix.ext; change ∀ i j, raw34233step1 i j = -(raw34233step0 i j); unfold raw34233step1 raw34233step0; decide +kernel
      have hl : raw34233step1Labels = raw34233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34233step1 raw34233step1Labels = mixedMoment B raw34233step2 raw34233step2Labels := by
      have ha : raw34233step2 = raw34233step1 := by apply Matrix.ext; unfold raw34233step2 raw34233step1; decide +kernel
      have hl : raw34233step1Labels = labelEmbedding1 ∘ raw34233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34233step1 raw34233step1Labels raw34233step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

def raw34234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34234 raw34234Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw34234 raw34234Labels = mixedMoment B raw34234step0 raw34234step0Labels := by
      have hz : ∀ j, raw34234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34234step0 = (fun i j => raw34234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34234step0 raw34234; decide +kernel
      have hl : raw34234step0Labels = raw34234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34234 raw34234Labels permutation346 hz
    mixedMoment B raw34234step0 raw34234step0Labels = mixedMoment B raw34234step1 raw34234step1Labels := by
      have ha : raw34234step1 = (fun i j => raw34234step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34234step1 raw34234step0; decide +kernel
      have hl : raw34234step1Labels = raw34234step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34234step0 raw34234step0Labels permutation35 permutation7
    mixedMoment B raw34234step1 raw34234step1Labels = mixedMoment B raw34234step2 raw34234step2Labels := by
      have ha : raw34234step2 = -raw34234step1 := by apply Matrix.ext; change ∀ i j, raw34234step2 i j = -(raw34234step1 i j); unfold raw34234step2 raw34234step1; decide +kernel
      have hl : raw34234step2Labels = raw34234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34234step2 raw34234step2Labels = mixedMoment B raw34234step3 raw34234step3Labels := by
      have ha : raw34234step3 = raw34234step2 := by apply Matrix.ext; unfold raw34234step3 raw34234step2; decide +kernel
      have hl : raw34234step2Labels = labelEmbedding1 ∘ raw34234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34234step2 raw34234step2Labels raw34234step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw34235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw34235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34235 raw34235Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw34235 raw34235Labels = mixedMoment B raw34235step0 raw34235step0Labels := by
      have hz : ∀ j, raw34235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34235step0 = (fun i j => raw34235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34235step0 raw34235; decide +kernel
      have hl : raw34235step0Labels = raw34235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34235 raw34235Labels permutation346 hz
    mixedMoment B raw34235step0 raw34235step0Labels = mixedMoment B raw34235step1 raw34235step1Labels := by
      have ha : raw34235step1 = (fun i j => raw34235step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34235step1 raw34235step0; decide +kernel
      have hl : raw34235step1Labels = raw34235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34235step0 raw34235step0Labels permutation35 permutation7
    mixedMoment B raw34235step1 raw34235step1Labels = mixedMoment B raw34235step2 raw34235step2Labels := by
      have ha : raw34235step2 = -raw34235step1 := by apply Matrix.ext; change ∀ i j, raw34235step2 i j = -(raw34235step1 i j); unfold raw34235step2 raw34235step1; decide +kernel
      have hl : raw34235step2Labels = raw34235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34235step2 raw34235step2Labels = mixedMoment B raw34235step3 raw34235step3Labels := by
      have ha : raw34235step3 = raw34235step2 := by apply Matrix.ext; unfold raw34235step3 raw34235step2; decide +kernel
      have hl : raw34235step2Labels = labelEmbedding1 ∘ raw34235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34235step2 raw34235step2Labels raw34235step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw34236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34236step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34236step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34236 raw34236Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw34236 raw34236Labels = mixedMoment B raw34236step0 raw34236step0Labels := by
      have hz : ∀ j, raw34236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34236step0 = (fun i j => raw34236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34236step0 raw34236; decide +kernel
      have hl : raw34236step0Labels = raw34236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34236 raw34236Labels permutation346 hz
    mixedMoment B raw34236step0 raw34236step0Labels = mixedMoment B raw34236step1 raw34236step1Labels := by
      have ha : raw34236step1 = (fun i j => raw34236step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34236step1 raw34236step0; decide +kernel
      have hl : raw34236step1Labels = raw34236step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34236step0 raw34236step0Labels permutation35 permutation7
    mixedMoment B raw34236step1 raw34236step1Labels = mixedMoment B raw34236step2 raw34236step2Labels := by
      have ha : raw34236step2 = -raw34236step1 := by apply Matrix.ext; change ∀ i j, raw34236step2 i j = -(raw34236step1 i j); unfold raw34236step2 raw34236step1; decide +kernel
      have hl : raw34236step2Labels = raw34236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34236step2 raw34236step2Labels = mixedMoment B raw34236step3 raw34236step3Labels := by
      have ha : raw34236step3 = raw34236step2 := by apply Matrix.ext; unfold raw34236step3 raw34236step2; decide +kernel
      have hl : raw34236step2Labels = labelEmbedding1 ∘ raw34236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34236step2 raw34236step2Labels raw34236step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw34237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw34237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34237 raw34237Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw34237 raw34237Labels = mixedMoment B raw34237step0 raw34237step0Labels := by
      have ha : raw34237step0 = (fun i j => raw34237 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34237step0 raw34237; decide +kernel
      have hl : raw34237step0Labels = raw34237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34237 raw34237Labels permutation155 permutation7
    mixedMoment B raw34237step0 raw34237step0Labels = mixedMoment B raw34237step1 raw34237step1Labels := by
      have ha : raw34237step1 = -raw34237step0 := by apply Matrix.ext; change ∀ i j, raw34237step1 i j = -(raw34237step0 i j); unfold raw34237step1 raw34237step0; decide +kernel
      have hl : raw34237step1Labels = raw34237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34237step1 raw34237step1Labels = mixedMoment B raw34237step2 raw34237step2Labels := by
      have ha : raw34237step2 = raw34237step1 := by apply Matrix.ext; unfold raw34237step2 raw34237step1; decide +kernel
      have hl : raw34237step1Labels = labelEmbedding1 ∘ raw34237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34237step1 raw34237step1Labels raw34237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

def raw34238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw34238step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw34238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34238step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw34238step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34238 raw34238Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw34238 raw34238Labels = mixedMoment B raw34238step0 raw34238step0Labels := by
      have hz : ∀ j, raw34238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34238step0 = (fun i j => raw34238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34238step0 raw34238; decide +kernel
      have hl : raw34238step0Labels = raw34238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34238 raw34238Labels permutation346 hz
    mixedMoment B raw34238step0 raw34238step0Labels = mixedMoment B raw34238step1 raw34238step1Labels := by
      have ha : raw34238step1 = (fun i j => raw34238step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34238step1 raw34238step0; decide +kernel
      have hl : raw34238step1Labels = raw34238step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34238step0 raw34238step0Labels permutation35 permutation7
    mixedMoment B raw34238step1 raw34238step1Labels = mixedMoment B raw34238step2 raw34238step2Labels := by
      have ha : raw34238step2 = -raw34238step1 := by apply Matrix.ext; change ∀ i j, raw34238step2 i j = -(raw34238step1 i j); unfold raw34238step2 raw34238step1; decide +kernel
      have hl : raw34238step2Labels = raw34238step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34238step2 raw34238step2Labels = mixedMoment B raw34238step3 raw34238step3Labels := by
      have ha : raw34238step3 = raw34238step2 := by apply Matrix.ext; unfold raw34238step3 raw34238step2; decide +kernel
      have hl : raw34238step2Labels = labelEmbedding1 ∘ raw34238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34238step2 raw34238step2Labels raw34238step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw34239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw34239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw34239step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw34239step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34239step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34239step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34239 raw34239Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw34239 raw34239Labels = mixedMoment B raw34239step0 raw34239step0Labels := by
      have hz : ∀ j, raw34239 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34239step0 = (fun i j => raw34239 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34239step0 raw34239; decide +kernel
      have hl : raw34239step0Labels = raw34239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34239 raw34239Labels permutation520 hz
    mixedMoment B raw34239step0 raw34239step0Labels = mixedMoment B raw34239step1 raw34239step1Labels := by
      have hz : ∀ j, raw34239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34239step1 = (fun i j => raw34239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34239step1 raw34239step0; decide +kernel
      have hl : raw34239step1Labels = raw34239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34239step0 raw34239step0Labels permutation80 hz
    mixedMoment B raw34239step1 raw34239step1Labels = mixedMoment B raw34239step2 raw34239step2Labels := by
      have ha : raw34239step2 = (fun i j => raw34239step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34239step2 raw34239step1; decide +kernel
      have hl : raw34239step2Labels = raw34239step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34239step1 raw34239step1Labels permutation9 permutation7
    mixedMoment B raw34239step2 raw34239step2Labels = mixedMoment B raw34239step3 raw34239step3Labels := by
      have ha : raw34239step3 = -raw34239step2 := by apply Matrix.ext; change ∀ i j, raw34239step3 i j = -(raw34239step2 i j); unfold raw34239step3 raw34239step2; decide +kernel
      have hl : raw34239step3Labels = raw34239step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34239step3 raw34239step3Labels = mixedMoment B raw34239step4 raw34239step4Labels := by
      have ha : raw34239step4 = raw34239step3 := by apply Matrix.ext; unfold raw34239step4 raw34239step3; decide +kernel
      have hl : raw34239step3Labels = labelEmbedding1 ∘ raw34239step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34239step3 raw34239step3Labels raw34239step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw34240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34240 raw34240Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw34240 raw34240Labels = mixedMoment B raw34240step0 raw34240step0Labels := by
      have hz : ∀ j, raw34240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34240step0 = (fun i j => raw34240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34240step0 raw34240; decide +kernel
      have hl : raw34240step0Labels = raw34240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34240 raw34240Labels permutation346 hz
    mixedMoment B raw34240step0 raw34240step0Labels = mixedMoment B raw34240step1 raw34240step1Labels := by
      have ha : raw34240step1 = (fun i j => raw34240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34240step1 raw34240step0; decide +kernel
      have hl : raw34240step1Labels = raw34240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34240step0 raw34240step0Labels permutation34 permutation2
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw34241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34241 raw34241Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw34241 raw34241Labels = mixedMoment B raw34241step0 raw34241step0Labels := by
      have ha : raw34241step0 = (fun i j => raw34241 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34241step0 raw34241; decide +kernel
      have hl : raw34241step0Labels = raw34241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34241 raw34241Labels permutation154 permutation2
    _ = mixedMoment B node1803 node1803Labels := by rfl

def raw34242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34242 raw34242Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw34242 raw34242Labels = mixedMoment B raw34242step0 raw34242step0Labels := by
      have hz : ∀ j, raw34242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34242step0 = (fun i j => raw34242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34242step0 raw34242; decide +kernel
      have hl : raw34242step0Labels = raw34242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34242 raw34242Labels permutation346 hz
    mixedMoment B raw34242step0 raw34242step0Labels = mixedMoment B raw34242step1 raw34242step1Labels := by
      have ha : raw34242step1 = (fun i j => raw34242step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34242step1 raw34242step0; decide +kernel
      have hl : raw34242step1Labels = raw34242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34242step0 raw34242step0Labels permutation35 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw34243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34243 raw34243Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw34243 raw34243Labels = mixedMoment B raw34243step0 raw34243step0Labels := by
      have hz : ∀ j, raw34243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34243step0 = (fun i j => raw34243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34243step0 raw34243; decide +kernel
      have hl : raw34243step0Labels = raw34243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34243 raw34243Labels permutation346 hz
    mixedMoment B raw34243step0 raw34243step0Labels = mixedMoment B raw34243step1 raw34243step1Labels := by
      have ha : raw34243step1 = (fun i j => raw34243step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34243step1 raw34243step0; decide +kernel
      have hl : raw34243step1Labels = raw34243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34243step0 raw34243step0Labels permutation34 permutation3
    mixedMoment B raw34243step1 raw34243step1Labels = mixedMoment B raw34243step2 raw34243step2Labels := by
      have ha : raw34243step2 = raw34243step1 := by apply Matrix.ext; unfold raw34243step2 raw34243step1; decide +kernel
      have hl : raw34243step1Labels = labelEmbedding6 ∘ raw34243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34243step1 raw34243step1Labels raw34243step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw34244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34244 raw34244Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw34244 raw34244Labels = mixedMoment B raw34244step0 raw34244step0Labels := by
      have ha : raw34244step0 = (fun i j => raw34244 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34244step0 raw34244; decide +kernel
      have hl : raw34244step0Labels = raw34244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34244 raw34244Labels permutation178 permutation3
    mixedMoment B raw34244step0 raw34244step0Labels = mixedMoment B raw34244step1 raw34244step1Labels := by
      have ha : raw34244step1 = raw34244step0 := by apply Matrix.ext; unfold raw34244step1 raw34244step0; decide +kernel
      have hl : raw34244step0Labels = labelEmbedding6 ∘ raw34244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34244step0 raw34244step0Labels raw34244step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw34245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34245step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34245step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34245 raw34245Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34245 raw34245Labels = mixedMoment B raw34245step0 raw34245step0Labels := by
      have hz : ∀ j, raw34245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34245step0 = (fun i j => raw34245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34245step0 raw34245; decide +kernel
      have hl : raw34245step0Labels = raw34245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34245 raw34245Labels permutation346 hz
    mixedMoment B raw34245step0 raw34245step0Labels = mixedMoment B raw34245step1 raw34245step1Labels := by
      have ha : raw34245step1 = (fun i j => raw34245step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34245step1 raw34245step0; decide +kernel
      have hl : raw34245step1Labels = raw34245step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34245step0 raw34245step0Labels permutation45 permutation5
    mixedMoment B raw34245step1 raw34245step1Labels = mixedMoment B raw34245step2 raw34245step2Labels := by
      have ha : raw34245step2 = -raw34245step1 := by apply Matrix.ext; change ∀ i j, raw34245step2 i j = -(raw34245step1 i j); unfold raw34245step2 raw34245step1; decide +kernel
      have hl : raw34245step2Labels = raw34245step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34245step2 raw34245step2Labels = mixedMoment B raw34245step3 raw34245step3Labels := by
      have ha : raw34245step3 = raw34245step2 := by apply Matrix.ext; unfold raw34245step3 raw34245step2; decide +kernel
      have hl : raw34245step2Labels = labelEmbedding8 ∘ raw34245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34245step2 raw34245step2Labels raw34245step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34246step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34246 raw34246Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw34246 raw34246Labels = mixedMoment B raw34246step0 raw34246step0Labels := by
      have hz : ∀ j, raw34246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34246step0 = (fun i j => raw34246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34246step0 raw34246; decide +kernel
      have hl : raw34246step0Labels = raw34246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34246 raw34246Labels permutation346 hz
    mixedMoment B raw34246step0 raw34246step0Labels = mixedMoment B raw34246step1 raw34246step1Labels := by
      have ha : raw34246step1 = (fun i j => raw34246step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34246step1 raw34246step0; decide +kernel
      have hl : raw34246step1Labels = raw34246step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34246step0 raw34246step0Labels permutation48 permutation5
    mixedMoment B raw34246step1 raw34246step1Labels = mixedMoment B raw34246step2 raw34246step2Labels := by
      have ha : raw34246step2 = -raw34246step1 := by apply Matrix.ext; change ∀ i j, raw34246step2 i j = -(raw34246step1 i j); unfold raw34246step2 raw34246step1; decide +kernel
      have hl : raw34246step2Labels = raw34246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34246step2 raw34246step2Labels = mixedMoment B raw34246step3 raw34246step3Labels := by
      have ha : raw34246step3 = raw34246step2 := by apply Matrix.ext; unfold raw34246step3 raw34246step2; decide +kernel
      have hl : raw34246step2Labels = labelEmbedding8 ∘ raw34246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34246step2 raw34246step2Labels raw34246step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw34247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34247 raw34247Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw34247 raw34247Labels = mixedMoment B raw34247step0 raw34247step0Labels := by
      have ha : raw34247step0 = (fun i j => raw34247 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34247step0 raw34247; decide +kernel
      have hl : raw34247step0Labels = raw34247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34247 raw34247Labels permutation164 permutation3
    mixedMoment B raw34247step0 raw34247step0Labels = mixedMoment B raw34247step1 raw34247step1Labels := by
      have ha : raw34247step1 = raw34247step0 := by apply Matrix.ext; unfold raw34247step1 raw34247step0; decide +kernel
      have hl : raw34247step0Labels = labelEmbedding6 ∘ raw34247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34247step0 raw34247step0Labels raw34247step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw34248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34248 raw34248Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34248 raw34248Labels = mixedMoment B raw34248step0 raw34248step0Labels := by
      have ha : raw34248step0 = (fun i j => raw34248 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34248step0 raw34248; decide +kernel
      have hl : raw34248step0Labels = raw34248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34248 raw34248Labels permutation164 permutation3
    mixedMoment B raw34248step0 raw34248step0Labels = mixedMoment B raw34248step1 raw34248step1Labels := by
      have ha : raw34248step1 = raw34248step0 := by apply Matrix.ext; unfold raw34248step1 raw34248step0; decide +kernel
      have hl : raw34248step0Labels = labelEmbedding6 ∘ raw34248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34248step0 raw34248step0Labels raw34248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw34249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34249 raw34249Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34249 raw34249Labels = mixedMoment B raw34249step0 raw34249step0Labels := by
      have ha : raw34249step0 = (fun i j => raw34249 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34249step0 raw34249; decide +kernel
      have hl : raw34249step0Labels = raw34249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34249 raw34249Labels permutation164 permutation3
    mixedMoment B raw34249step0 raw34249step0Labels = mixedMoment B raw34249step1 raw34249step1Labels := by
      have ha : raw34249step1 = raw34249step0 := by apply Matrix.ext; unfold raw34249step1 raw34249step0; decide +kernel
      have hl : raw34249step0Labels = labelEmbedding6 ∘ raw34249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34249step0 raw34249step0Labels raw34249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw34250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34250 raw34250Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34250 raw34250Labels = mixedMoment B raw34250step0 raw34250step0Labels := by
      have ha : raw34250step0 = (fun i j => raw34250 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34250step0 raw34250; decide +kernel
      have hl : raw34250step0Labels = raw34250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34250 raw34250Labels permutation168 permutation3
    mixedMoment B raw34250step0 raw34250step0Labels = mixedMoment B raw34250step1 raw34250step1Labels := by
      have ha : raw34250step1 = raw34250step0 := by apply Matrix.ext; unfold raw34250step1 raw34250step0; decide +kernel
      have hl : raw34250step0Labels = labelEmbedding6 ∘ raw34250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34250step0 raw34250step0Labels raw34250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34251 raw34251Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw34251 raw34251Labels = mixedMoment B raw34251step0 raw34251step0Labels := by
      have hz : ∀ j, raw34251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34251step0 = (fun i j => raw34251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34251step0 raw34251; decide +kernel
      have hl : raw34251step0Labels = raw34251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34251 raw34251Labels permutation346 hz
    mixedMoment B raw34251step0 raw34251step0Labels = mixedMoment B raw34251step1 raw34251step1Labels := by
      have ha : raw34251step1 = (fun i j => raw34251step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34251step1 raw34251step0; decide +kernel
      have hl : raw34251step1Labels = raw34251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34251step0 raw34251step0Labels permutation35 permutation3
    mixedMoment B raw34251step1 raw34251step1Labels = mixedMoment B raw34251step2 raw34251step2Labels := by
      have ha : raw34251step2 = raw34251step1 := by apply Matrix.ext; unfold raw34251step2 raw34251step1; decide +kernel
      have hl : raw34251step1Labels = labelEmbedding6 ∘ raw34251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34251step1 raw34251step1Labels raw34251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw34252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34252 raw34252Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw34252 raw34252Labels = mixedMoment B raw34252step0 raw34252step0Labels := by
      have hz : ∀ j, raw34252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34252step0 = (fun i j => raw34252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34252step0 raw34252; decide +kernel
      have hl : raw34252step0Labels = raw34252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34252 raw34252Labels permutation346 hz
    mixedMoment B raw34252step0 raw34252step0Labels = mixedMoment B raw34252step1 raw34252step1Labels := by
      have ha : raw34252step1 = (fun i j => raw34252step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34252step1 raw34252step0; decide +kernel
      have hl : raw34252step1Labels = raw34252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34252step0 raw34252step0Labels permutation35 permutation3
    mixedMoment B raw34252step1 raw34252step1Labels = mixedMoment B raw34252step2 raw34252step2Labels := by
      have ha : raw34252step2 = raw34252step1 := by apply Matrix.ext; unfold raw34252step2 raw34252step1; decide +kernel
      have hl : raw34252step1Labels = labelEmbedding6 ∘ raw34252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34252step1 raw34252step1Labels raw34252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw34253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw34253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34253 raw34253Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw34253 raw34253Labels = mixedMoment B raw34253step0 raw34253step0Labels := by
      have ha : raw34253step0 = (fun i j => raw34253 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34253step0 raw34253; decide +kernel
      have hl : raw34253step0Labels = raw34253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34253 raw34253Labels permutation179 permutation3
    mixedMoment B raw34253step0 raw34253step0Labels = mixedMoment B raw34253step1 raw34253step1Labels := by
      have ha : raw34253step1 = raw34253step0 := by apply Matrix.ext; unfold raw34253step1 raw34253step0; decide +kernel
      have hl : raw34253step0Labels = labelEmbedding6 ∘ raw34253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34253step0 raw34253step0Labels raw34253step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

def raw34254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw34254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw34254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34254step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34254step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34254 raw34254Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw34254 raw34254Labels = mixedMoment B raw34254step0 raw34254step0Labels := by
      have hz : ∀ j, raw34254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34254step0 = (fun i j => raw34254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34254step0 raw34254; decide +kernel
      have hl : raw34254step0Labels = raw34254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34254 raw34254Labels permutation346 hz
    mixedMoment B raw34254step0 raw34254step0Labels = mixedMoment B raw34254step1 raw34254step1Labels := by
      have ha : raw34254step1 = (fun i j => raw34254step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34254step1 raw34254step0; decide +kernel
      have hl : raw34254step1Labels = raw34254step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34254step0 raw34254step0Labels permutation45 permutation5
    mixedMoment B raw34254step1 raw34254step1Labels = mixedMoment B raw34254step2 raw34254step2Labels := by
      have ha : raw34254step2 = -raw34254step1 := by apply Matrix.ext; change ∀ i j, raw34254step2 i j = -(raw34254step1 i j); unfold raw34254step2 raw34254step1; decide +kernel
      have hl : raw34254step2Labels = raw34254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34254step2 raw34254step2Labels = mixedMoment B raw34254step3 raw34254step3Labels := by
      have ha : raw34254step3 = raw34254step2 := by apply Matrix.ext; unfold raw34254step3 raw34254step2; decide +kernel
      have hl : raw34254step2Labels = labelEmbedding8 ∘ raw34254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34254step2 raw34254step2Labels raw34254step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw34255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34255 raw34255Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw34255 raw34255Labels = mixedMoment B raw34255step0 raw34255step0Labels := by
      have hz : ∀ j, raw34255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34255step0 = (fun i j => raw34255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34255step0 raw34255; decide +kernel
      have hl : raw34255step0Labels = raw34255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34255 raw34255Labels permutation346 hz
    mixedMoment B raw34255step0 raw34255step0Labels = mixedMoment B raw34255step1 raw34255step1Labels := by
      have ha : raw34255step1 = (fun i j => raw34255step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34255step1 raw34255step0; decide +kernel
      have hl : raw34255step1Labels = raw34255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34255step0 raw34255step0Labels permutation35 permutation3
    mixedMoment B raw34255step1 raw34255step1Labels = mixedMoment B raw34255step2 raw34255step2Labels := by
      have ha : raw34255step2 = raw34255step1 := by apply Matrix.ext; unfold raw34255step2 raw34255step1; decide +kernel
      have hl : raw34255step1Labels = labelEmbedding6 ∘ raw34255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34255step1 raw34255step1Labels raw34255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw34256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34256 raw34256Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw34256 raw34256Labels = mixedMoment B raw34256step0 raw34256step0Labels := by
      have hz : ∀ j, raw34256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34256step0 = (fun i j => raw34256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34256step0 raw34256; decide +kernel
      have hl : raw34256step0Labels = raw34256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34256 raw34256Labels permutation346 hz
    mixedMoment B raw34256step0 raw34256step0Labels = mixedMoment B raw34256step1 raw34256step1Labels := by
      have ha : raw34256step1 = (fun i j => raw34256step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34256step1 raw34256step0; decide +kernel
      have hl : raw34256step1Labels = raw34256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34256step0 raw34256step0Labels permutation32 permutation3
    mixedMoment B raw34256step1 raw34256step1Labels = mixedMoment B raw34256step2 raw34256step2Labels := by
      have ha : raw34256step2 = raw34256step1 := by apply Matrix.ext; unfold raw34256step2 raw34256step1; decide +kernel
      have hl : raw34256step1Labels = labelEmbedding6 ∘ raw34256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34256step1 raw34256step1Labels raw34256step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

def raw34257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34257 raw34257Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw34257 raw34257Labels = mixedMoment B raw34257step0 raw34257step0Labels := by
      have hz : ∀ j, raw34257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34257step0 = (fun i j => raw34257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34257step0 raw34257; decide +kernel
      have hl : raw34257step0Labels = raw34257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34257 raw34257Labels permutation346 hz
    mixedMoment B raw34257step0 raw34257step0Labels = mixedMoment B raw34257step1 raw34257step1Labels := by
      have ha : raw34257step1 = (fun i j => raw34257step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34257step1 raw34257step0; decide +kernel
      have hl : raw34257step1Labels = raw34257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34257step0 raw34257step0Labels permutation32 permutation3
    mixedMoment B raw34257step1 raw34257step1Labels = mixedMoment B raw34257step2 raw34257step2Labels := by
      have ha : raw34257step2 = raw34257step1 := by apply Matrix.ext; unfold raw34257step2 raw34257step1; decide +kernel
      have hl : raw34257step1Labels = labelEmbedding6 ∘ raw34257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34257step1 raw34257step1Labels raw34257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

def raw34258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw34258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34258 raw34258Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw34258 raw34258Labels = mixedMoment B raw34258step0 raw34258step0Labels := by
      have ha : raw34258step0 = (fun i j => raw34258 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34258step0 raw34258; decide +kernel
      have hl : raw34258step0Labels = raw34258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34258 raw34258Labels permutation176 permutation3
    mixedMoment B raw34258step0 raw34258step0Labels = mixedMoment B raw34258step1 raw34258step1Labels := by
      have ha : raw34258step1 = raw34258step0 := by apply Matrix.ext; unfold raw34258step1 raw34258step0; decide +kernel
      have hl : raw34258step0Labels = labelEmbedding6 ∘ raw34258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34258step0 raw34258step0Labels raw34258step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

def raw34259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw34259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34259 raw34259Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34259 raw34259Labels = mixedMoment B raw34259step0 raw34259step0Labels := by
      have hz : ∀ j, raw34259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34259step0 = (fun i j => raw34259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34259step0 raw34259; decide +kernel
      have hl : raw34259step0Labels = raw34259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34259 raw34259Labels permutation346 hz
    mixedMoment B raw34259step0 raw34259step0Labels = mixedMoment B raw34259step1 raw34259step1Labels := by
      have ha : raw34259step1 = (fun i j => raw34259step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34259step1 raw34259step0; decide +kernel
      have hl : raw34259step1Labels = raw34259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34259step0 raw34259step0Labels permutation36 permutation3
    mixedMoment B raw34259step1 raw34259step1Labels = mixedMoment B raw34259step2 raw34259step2Labels := by
      have ha : raw34259step2 = raw34259step1 := by apply Matrix.ext; unfold raw34259step2 raw34259step1; decide +kernel
      have hl : raw34259step1Labels = labelEmbedding6 ∘ raw34259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34259step1 raw34259step1Labels raw34259step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34260 raw34260Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw34260 raw34260Labels = mixedMoment B raw34260step0 raw34260step0Labels := by
      have hz : ∀ j, raw34260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34260step0 = (fun i j => raw34260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34260step0 raw34260; decide +kernel
      have hl : raw34260step0Labels = raw34260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34260 raw34260Labels permutation346 hz
    mixedMoment B raw34260step0 raw34260step0Labels = mixedMoment B raw34260step1 raw34260step1Labels := by
      have ha : raw34260step1 = (fun i j => raw34260step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34260step1 raw34260step0; decide +kernel
      have hl : raw34260step1Labels = raw34260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34260step0 raw34260step0Labels permutation34 permutation3
    mixedMoment B raw34260step1 raw34260step1Labels = mixedMoment B raw34260step2 raw34260step2Labels := by
      have ha : raw34260step2 = raw34260step1 := by apply Matrix.ext; unfold raw34260step2 raw34260step1; decide +kernel
      have hl : raw34260step1Labels = labelEmbedding6 ∘ raw34260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34260step1 raw34260step1Labels raw34260step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw34261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34261 raw34261Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw34261 raw34261Labels = mixedMoment B raw34261step0 raw34261step0Labels := by
      have hz : ∀ j, raw34261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34261step0 = (fun i j => raw34261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34261step0 raw34261; decide +kernel
      have hl : raw34261step0Labels = raw34261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34261 raw34261Labels permutation346 hz
    mixedMoment B raw34261step0 raw34261step0Labels = mixedMoment B raw34261step1 raw34261step1Labels := by
      have ha : raw34261step1 = (fun i j => raw34261step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34261step1 raw34261step0; decide +kernel
      have hl : raw34261step1Labels = raw34261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34261step0 raw34261step0Labels permutation34 permutation3
    mixedMoment B raw34261step1 raw34261step1Labels = mixedMoment B raw34261step2 raw34261step2Labels := by
      have ha : raw34261step2 = raw34261step1 := by apply Matrix.ext; unfold raw34261step2 raw34261step1; decide +kernel
      have hl : raw34261step1Labels = labelEmbedding6 ∘ raw34261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34261step1 raw34261step1Labels raw34261step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw34262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw34262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw34262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34262 raw34262Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw34262 raw34262Labels = mixedMoment B raw34262step0 raw34262step0Labels := by
      have ha : raw34262step0 = (fun i j => raw34262 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34262step0 raw34262; decide +kernel
      have hl : raw34262step0Labels = raw34262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34262 raw34262Labels permutation178 permutation3
    mixedMoment B raw34262step0 raw34262step0Labels = mixedMoment B raw34262step1 raw34262step1Labels := by
      have ha : raw34262step1 = raw34262step0 := by apply Matrix.ext; unfold raw34262step1 raw34262step0; decide +kernel
      have hl : raw34262step0Labels = labelEmbedding6 ∘ raw34262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34262step0 raw34262step0Labels raw34262step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

def raw34263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw34263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34263 raw34263Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw34263 raw34263Labels = mixedMoment B raw34263step0 raw34263step0Labels := by
      have hz : ∀ j, raw34263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34263step0 = (fun i j => raw34263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34263step0 raw34263; decide +kernel
      have hl : raw34263step0Labels = raw34263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34263 raw34263Labels permutation346 hz
    mixedMoment B raw34263step0 raw34263step0Labels = mixedMoment B raw34263step1 raw34263step1Labels := by
      have ha : raw34263step1 = (fun i j => raw34263step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34263step1 raw34263step0; decide +kernel
      have hl : raw34263step1Labels = raw34263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34263step0 raw34263step0Labels permutation34 permutation3
    mixedMoment B raw34263step1 raw34263step1Labels = mixedMoment B raw34263step2 raw34263step2Labels := by
      have ha : raw34263step2 = raw34263step1 := by apply Matrix.ext; unfold raw34263step2 raw34263step1; decide +kernel
      have hl : raw34263step1Labels = labelEmbedding6 ∘ raw34263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34263step1 raw34263step1Labels raw34263step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw34264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34264step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34264 raw34264Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw34264 raw34264Labels = mixedMoment B raw34264step0 raw34264step0Labels := by
      have hz : ∀ j, raw34264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34264step0 = (fun i j => raw34264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34264step0 raw34264; decide +kernel
      have hl : raw34264step0Labels = raw34264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34264 raw34264Labels permutation346 hz
    mixedMoment B raw34264step0 raw34264step0Labels = mixedMoment B raw34264step1 raw34264step1Labels := by
      have ha : raw34264step1 = (fun i j => raw34264step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34264step1 raw34264step0; decide +kernel
      have hl : raw34264step1Labels = raw34264step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34264step0 raw34264step0Labels permutation35 permutation4
    mixedMoment B raw34264step1 raw34264step1Labels = mixedMoment B raw34264step2 raw34264step2Labels := by
      have ha : raw34264step2 = -raw34264step1 := by apply Matrix.ext; change ∀ i j, raw34264step2 i j = -(raw34264step1 i j); unfold raw34264step2 raw34264step1; decide +kernel
      have hl : raw34264step2Labels = raw34264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34264step2 raw34264step2Labels = mixedMoment B raw34264step3 raw34264step3Labels := by
      have ha : raw34264step3 = raw34264step2 := by apply Matrix.ext; unfold raw34264step3 raw34264step2; decide +kernel
      have hl : raw34264step2Labels = labelEmbedding7 ∘ raw34264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34264step2 raw34264step2Labels raw34264step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw34265 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34265step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34265 raw34265Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw34265 raw34265Labels = mixedMoment B raw34265step0 raw34265step0Labels := by
      have hz : ∀ j, raw34265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34265step0 = (fun i j => raw34265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34265step0 raw34265; decide +kernel
      have hl : raw34265step0Labels = raw34265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34265 raw34265Labels permutation346 hz
    mixedMoment B raw34265step0 raw34265step0Labels = mixedMoment B raw34265step1 raw34265step1Labels := by
      have ha : raw34265step1 = (fun i j => raw34265step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34265step1 raw34265step0; decide +kernel
      have hl : raw34265step1Labels = raw34265step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34265step0 raw34265step0Labels permutation35 permutation4
    mixedMoment B raw34265step1 raw34265step1Labels = mixedMoment B raw34265step2 raw34265step2Labels := by
      have ha : raw34265step2 = -raw34265step1 := by apply Matrix.ext; change ∀ i j, raw34265step2 i j = -(raw34265step1 i j); unfold raw34265step2 raw34265step1; decide +kernel
      have hl : raw34265step2Labels = raw34265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34265step2 raw34265step2Labels = mixedMoment B raw34265step3 raw34265step3Labels := by
      have ha : raw34265step3 = raw34265step2 := by apply Matrix.ext; unfold raw34265step3 raw34265step2; decide +kernel
      have hl : raw34265step2Labels = labelEmbedding7 ∘ raw34265step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34265step2 raw34265step2Labels raw34265step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw34266 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw34266step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw34266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34266 raw34266Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw34266 raw34266Labels = mixedMoment B raw34266step0 raw34266step0Labels := by
      have ha : raw34266step0 = (fun i j => raw34266 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34266step0 raw34266; decide +kernel
      have hl : raw34266step0Labels = raw34266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34266 raw34266Labels permutation179 permutation4
    mixedMoment B raw34266step0 raw34266step0Labels = mixedMoment B raw34266step1 raw34266step1Labels := by
      have ha : raw34266step1 = -raw34266step0 := by apply Matrix.ext; change ∀ i j, raw34266step1 i j = -(raw34266step0 i j); unfold raw34266step1 raw34266step0; decide +kernel
      have hl : raw34266step1Labels = raw34266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34266step1 raw34266step1Labels = mixedMoment B raw34266step2 raw34266step2Labels := by
      have ha : raw34266step2 = raw34266step1 := by apply Matrix.ext; unfold raw34266step2 raw34266step1; decide +kernel
      have hl : raw34266step1Labels = labelEmbedding7 ∘ raw34266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34266step1 raw34266step1Labels raw34266step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw34267 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw34267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw34267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34267 raw34267Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw34267 raw34267Labels = mixedMoment B raw34267step0 raw34267step0Labels := by
      have hz : ∀ j, raw34267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34267step0 = (fun i j => raw34267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34267step0 raw34267; decide +kernel
      have hl : raw34267step0Labels = raw34267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34267 raw34267Labels permutation346 hz
    mixedMoment B raw34267step0 raw34267step0Labels = mixedMoment B raw34267step1 raw34267step1Labels := by
      have ha : raw34267step1 = (fun i j => raw34267step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34267step1 raw34267step0; decide +kernel
      have hl : raw34267step1Labels = raw34267step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34267step0 raw34267step0Labels permutation34 permutation6
    mixedMoment B raw34267step1 raw34267step1Labels = mixedMoment B raw34267step2 raw34267step2Labels := by
      have ha : raw34267step2 = raw34267step1 := by apply Matrix.ext; unfold raw34267step2 raw34267step1; decide +kernel
      have hl : raw34267step1Labels = labelEmbedding9 ∘ raw34267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34267step1 raw34267step1Labels raw34267step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4829 node4829Labels := by rfl

def raw34268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34268step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34268 raw34268Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw34268 raw34268Labels = mixedMoment B raw34268step0 raw34268step0Labels := by
      have hz : ∀ j, raw34268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34268step0 = (fun i j => raw34268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34268step0 raw34268; decide +kernel
      have hl : raw34268step0Labels = raw34268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34268 raw34268Labels permutation346 hz
    mixedMoment B raw34268step0 raw34268step0Labels = mixedMoment B raw34268step1 raw34268step1Labels := by
      have ha : raw34268step1 = (fun i j => raw34268step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34268step1 raw34268step0; decide +kernel
      have hl : raw34268step1Labels = raw34268step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34268step0 raw34268step0Labels permutation34 permutation4
    mixedMoment B raw34268step1 raw34268step1Labels = mixedMoment B raw34268step2 raw34268step2Labels := by
      have ha : raw34268step2 = -raw34268step1 := by apply Matrix.ext; change ∀ i j, raw34268step2 i j = -(raw34268step1 i j); unfold raw34268step2 raw34268step1; decide +kernel
      have hl : raw34268step2Labels = raw34268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34268step2 raw34268step2Labels = mixedMoment B raw34268step3 raw34268step3Labels := by
      have ha : raw34268step3 = raw34268step2 := by apply Matrix.ext; unfold raw34268step3 raw34268step2; decide +kernel
      have hl : raw34268step2Labels = labelEmbedding7 ∘ raw34268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34268step2 raw34268step2Labels raw34268step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw34269 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34269step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34269 raw34269Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw34269 raw34269Labels = mixedMoment B raw34269step0 raw34269step0Labels := by
      have hz : ∀ j, raw34269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34269step0 = (fun i j => raw34269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34269step0 raw34269; decide +kernel
      have hl : raw34269step0Labels = raw34269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34269 raw34269Labels permutation346 hz
    mixedMoment B raw34269step0 raw34269step0Labels = mixedMoment B raw34269step1 raw34269step1Labels := by
      have ha : raw34269step1 = (fun i j => raw34269step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34269step1 raw34269step0; decide +kernel
      have hl : raw34269step1Labels = raw34269step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34269step0 raw34269step0Labels permutation34 permutation4
    mixedMoment B raw34269step1 raw34269step1Labels = mixedMoment B raw34269step2 raw34269step2Labels := by
      have ha : raw34269step2 = -raw34269step1 := by apply Matrix.ext; change ∀ i j, raw34269step2 i j = -(raw34269step1 i j); unfold raw34269step2 raw34269step1; decide +kernel
      have hl : raw34269step2Labels = raw34269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34269step2 raw34269step2Labels = mixedMoment B raw34269step3 raw34269step3Labels := by
      have ha : raw34269step3 = raw34269step2 := by apply Matrix.ext; unfold raw34269step3 raw34269step2; decide +kernel
      have hl : raw34269step2Labels = labelEmbedding7 ∘ raw34269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34269step2 raw34269step2Labels raw34269step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

def raw34270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34270step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34270step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34270 raw34270Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw34270 raw34270Labels = mixedMoment B raw34270step0 raw34270step0Labels := by
      have hz : ∀ j, raw34270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34270step0 = (fun i j => raw34270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34270step0 raw34270; decide +kernel
      have hl : raw34270step0Labels = raw34270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34270 raw34270Labels permutation346 hz
    mixedMoment B raw34270step0 raw34270step0Labels = mixedMoment B raw34270step1 raw34270step1Labels := by
      have ha : raw34270step1 = (fun i j => raw34270step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34270step1 raw34270step0; decide +kernel
      have hl : raw34270step1Labels = raw34270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34270step0 raw34270step0Labels permutation32 permutation7
    mixedMoment B raw34270step1 raw34270step1Labels = mixedMoment B raw34270step2 raw34270step2Labels := by
      have ha : raw34270step2 = -raw34270step1 := by apply Matrix.ext; change ∀ i j, raw34270step2 i j = -(raw34270step1 i j); unfold raw34270step2 raw34270step1; decide +kernel
      have hl : raw34270step2Labels = raw34270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34270step2 raw34270step2Labels = mixedMoment B raw34270step3 raw34270step3Labels := by
      have ha : raw34270step3 = raw34270step2 := by apply Matrix.ext; unfold raw34270step3 raw34270step2; decide +kernel
      have hl : raw34270step2Labels = labelEmbedding10 ∘ raw34270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34270step2 raw34270step2Labels raw34270step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw34271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34271step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34271 raw34271Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw34271 raw34271Labels = mixedMoment B raw34271step0 raw34271step0Labels := by
      have ha : raw34271step0 = (fun i j => raw34271 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34271step0 raw34271; decide +kernel
      have hl : raw34271step0Labels = raw34271Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34271 raw34271Labels permutation152 permutation7
    mixedMoment B raw34271step0 raw34271step0Labels = mixedMoment B raw34271step1 raw34271step1Labels := by
      have ha : raw34271step1 = -raw34271step0 := by apply Matrix.ext; change ∀ i j, raw34271step1 i j = -(raw34271step0 i j); unfold raw34271step1 raw34271step0; decide +kernel
      have hl : raw34271step1Labels = raw34271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34271step1 raw34271step1Labels = mixedMoment B raw34271step2 raw34271step2Labels := by
      have ha : raw34271step2 = raw34271step1 := by apply Matrix.ext; unfold raw34271step2 raw34271step1; decide +kernel
      have hl : raw34271step1Labels = labelEmbedding10 ∘ raw34271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34271step1 raw34271step1Labels raw34271step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw34272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34272step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34272 raw34272Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw34272 raw34272Labels = mixedMoment B raw34272step0 raw34272step0Labels := by
      have hz : ∀ j, raw34272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34272step0 = (fun i j => raw34272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34272step0 raw34272; decide +kernel
      have hl : raw34272step0Labels = raw34272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34272 raw34272Labels permutation346 hz
    mixedMoment B raw34272step0 raw34272step0Labels = mixedMoment B raw34272step1 raw34272step1Labels := by
      have ha : raw34272step1 = (fun i j => raw34272step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34272step1 raw34272step0; decide +kernel
      have hl : raw34272step1Labels = raw34272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34272step0 raw34272step0Labels permutation32 permutation7
    mixedMoment B raw34272step1 raw34272step1Labels = mixedMoment B raw34272step2 raw34272step2Labels := by
      have ha : raw34272step2 = -raw34272step1 := by apply Matrix.ext; change ∀ i j, raw34272step2 i j = -(raw34272step1 i j); unfold raw34272step2 raw34272step1; decide +kernel
      have hl : raw34272step2Labels = raw34272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34272step2 raw34272step2Labels = mixedMoment B raw34272step3 raw34272step3Labels := by
      have ha : raw34272step3 = raw34272step2 := by apply Matrix.ext; unfold raw34272step3 raw34272step2; decide +kernel
      have hl : raw34272step2Labels = labelEmbedding10 ∘ raw34272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34272step2 raw34272step2Labels raw34272step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw34273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34273step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34273 raw34273Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw34273 raw34273Labels = mixedMoment B raw34273step0 raw34273step0Labels := by
      have hz : ∀ j, raw34273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34273step0 = (fun i j => raw34273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34273step0 raw34273; decide +kernel
      have hl : raw34273step0Labels = raw34273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34273 raw34273Labels permutation346 hz
    mixedMoment B raw34273step0 raw34273step0Labels = mixedMoment B raw34273step1 raw34273step1Labels := by
      have ha : raw34273step1 = (fun i j => raw34273step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34273step1 raw34273step0; decide +kernel
      have hl : raw34273step1Labels = raw34273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34273step0 raw34273step0Labels permutation34 permutation7
    mixedMoment B raw34273step1 raw34273step1Labels = mixedMoment B raw34273step2 raw34273step2Labels := by
      have ha : raw34273step2 = -raw34273step1 := by apply Matrix.ext; change ∀ i j, raw34273step2 i j = -(raw34273step1 i j); unfold raw34273step2 raw34273step1; decide +kernel
      have hl : raw34273step2Labels = raw34273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34273step2 raw34273step2Labels = mixedMoment B raw34273step3 raw34273step3Labels := by
      have ha : raw34273step3 = raw34273step2 := by apply Matrix.ext; unfold raw34273step3 raw34273step2; decide +kernel
      have hl : raw34273step2Labels = labelEmbedding10 ∘ raw34273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34273step2 raw34273step2Labels raw34273step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw34274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34274step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34274step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34274step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34274 raw34274Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw34274 raw34274Labels = mixedMoment B raw34274step0 raw34274step0Labels := by
      have hz : ∀ j, raw34274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34274step0 = (fun i j => raw34274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34274step0 raw34274; decide +kernel
      have hl : raw34274step0Labels = raw34274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34274 raw34274Labels permutation346 hz
    mixedMoment B raw34274step0 raw34274step0Labels = mixedMoment B raw34274step1 raw34274step1Labels := by
      have ha : raw34274step1 = (fun i j => raw34274step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34274step1 raw34274step0; decide +kernel
      have hl : raw34274step1Labels = raw34274step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34274step0 raw34274step0Labels permutation32 permutation7
    mixedMoment B raw34274step1 raw34274step1Labels = mixedMoment B raw34274step2 raw34274step2Labels := by
      have ha : raw34274step2 = -raw34274step1 := by apply Matrix.ext; change ∀ i j, raw34274step2 i j = -(raw34274step1 i j); unfold raw34274step2 raw34274step1; decide +kernel
      have hl : raw34274step2Labels = raw34274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34274step2 raw34274step2Labels = mixedMoment B raw34274step3 raw34274step3Labels := by
      have ha : raw34274step3 = raw34274step2 := by apply Matrix.ext; unfold raw34274step3 raw34274step2; decide +kernel
      have hl : raw34274step2Labels = labelEmbedding10 ∘ raw34274step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34274step2 raw34274step2Labels raw34274step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw34275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34275 raw34275Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw34275 raw34275Labels = mixedMoment B raw34275step0 raw34275step0Labels := by
      have hz : ∀ j, raw34275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34275step0 = (fun i j => raw34275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34275step0 raw34275; decide +kernel
      have hl : raw34275step0Labels = raw34275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34275 raw34275Labels permutation346 hz
    mixedMoment B raw34275step0 raw34275step0Labels = mixedMoment B raw34275step1 raw34275step1Labels := by
      have hz : ∀ j, raw34275step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34275step1 = (fun i j => raw34275step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34275step1 raw34275step0; decide +kernel
      have hl : raw34275step1Labels = raw34275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34275step0 raw34275step0Labels permutation56 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw34276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34276 raw34276Labels = mixedMoment B node4679 node4679Labels := by
  calc
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw34277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34277 raw34277Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw34277 raw34277Labels = mixedMoment B raw34277step0 raw34277step0Labels := by
      have ha : raw34277step0 = (fun i j => raw34277 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34277step0 raw34277; decide +kernel
      have hl : raw34277step0Labels = raw34277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34277 raw34277Labels permutation158 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw34278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34278 raw34278Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw34278 raw34278Labels = mixedMoment B raw34278step0 raw34278step0Labels := by
      have ha : raw34278step0 = (fun i j => raw34278 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34278step0 raw34278; decide +kernel
      have hl : raw34278step0Labels = raw34278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34278 raw34278Labels permutation164 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw34279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34279 raw34279Labels = mixedMoment B node4833 node4833Labels := by
  calc
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw34280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34280 raw34280Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw34280 raw34280Labels = mixedMoment B raw34280step0 raw34280step0Labels := by
      have hz : ∀ j, raw34280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34280step0 = (fun i j => raw34280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34280step0 raw34280; decide +kernel
      have hl : raw34280step0Labels = raw34280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34280 raw34280Labels permutation346 hz
    mixedMoment B raw34280step0 raw34280step0Labels = mixedMoment B raw34280step1 raw34280step1Labels := by
      have ha : raw34280step1 = (fun i j => raw34280step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34280step1 raw34280step0; decide +kernel
      have hl : raw34280step1Labels = raw34280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34280step0 raw34280step0Labels permutation34 permutation2
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw34281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34281 raw34281Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw34281 raw34281Labels = mixedMoment B raw34281step0 raw34281step0Labels := by
      have ha : raw34281step0 = (fun i j => raw34281 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34281step0 raw34281; decide +kernel
      have hl : raw34281step0Labels = raw34281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34281 raw34281Labels permutation154 permutation2
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw34282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw34282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34282 raw34282Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw34282 raw34282Labels = mixedMoment B raw34282step0 raw34282step0Labels := by
      have hz : ∀ j, raw34282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34282step0 = (fun i j => raw34282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34282step0 raw34282; decide +kernel
      have hl : raw34282step0Labels = raw34282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34282 raw34282Labels permutation346 hz
    mixedMoment B raw34282step0 raw34282step0Labels = mixedMoment B raw34282step1 raw34282step1Labels := by
      have ha : raw34282step1 = (fun i j => raw34282step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34282step1 raw34282step0; decide +kernel
      have hl : raw34282step1Labels = raw34282step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34282step0 raw34282step0Labels permutation34 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw34283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34283 raw34283Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw34283 raw34283Labels = mixedMoment B raw34283step0 raw34283step0Labels := by
      have hz : ∀ j, raw34283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34283step0 = (fun i j => raw34283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34283step0 raw34283; decide +kernel
      have hl : raw34283step0Labels = raw34283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34283 raw34283Labels permutation346 hz
    mixedMoment B raw34283step0 raw34283step0Labels = mixedMoment B raw34283step1 raw34283step1Labels := by
      have ha : raw34283step1 = (fun i j => raw34283step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34283step1 raw34283step0; decide +kernel
      have hl : raw34283step1Labels = raw34283step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34283step0 raw34283step0Labels permutation35 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw34284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34284 raw34284Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw34284 raw34284Labels = mixedMoment B raw34284step0 raw34284step0Labels := by
      have hz : ∀ j, raw34284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34284step0 = (fun i j => raw34284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34284step0 raw34284; decide +kernel
      have hl : raw34284step0Labels = raw34284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34284 raw34284Labels permutation346 hz
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw34285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34285 raw34285Labels = mixedMoment B node4767 node4767Labels := by
  calc
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw34286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34286 raw34286Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw34286 raw34286Labels = mixedMoment B raw34286step0 raw34286step0Labels := by
      have hz : ∀ j, raw34286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34286step0 = (fun i j => raw34286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34286step0 raw34286; decide +kernel
      have hl : raw34286step0Labels = raw34286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34286 raw34286Labels permutation346 hz
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw34287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw34287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34287 raw34287Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw34287 raw34287Labels = mixedMoment B raw34287step0 raw34287step0Labels := by
      have hz : ∀ j, raw34287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34287step0 = (fun i j => raw34287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34287step0 raw34287; decide +kernel
      have hl : raw34287step0Labels = raw34287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34287 raw34287Labels permutation346 hz
    mixedMoment B raw34287step0 raw34287step0Labels = mixedMoment B raw34287step1 raw34287step1Labels := by
      have ha : raw34287step1 = (fun i j => raw34287step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34287step1 raw34287step0; decide +kernel
      have hl : raw34287step1Labels = raw34287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34287step0 raw34287step0Labels permutation33 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw34288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34288 raw34288Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw34288 raw34288Labels = mixedMoment B raw34288step0 raw34288step0Labels := by
      have hz : ∀ j, raw34288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34288step0 = (fun i j => raw34288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34288step0 raw34288; decide +kernel
      have hl : raw34288step0Labels = raw34288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34288 raw34288Labels permutation346 hz
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw34289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34289 raw34289Labels = mixedMoment B node4764 node4764Labels := by
  calc
    _ = mixedMoment B node4764 node4764Labels := by rfl

def raw34290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34290 raw34290Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw34290 raw34290Labels = mixedMoment B raw34290step0 raw34290step0Labels := by
      have hz : ∀ j, raw34290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34290step0 = (fun i j => raw34290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34290step0 raw34290; decide +kernel
      have hl : raw34290step0Labels = raw34290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34290 raw34290Labels permutation346 hz
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw34291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw34291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34291 raw34291Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw34291 raw34291Labels = mixedMoment B raw34291step0 raw34291step0Labels := by
      have hz : ∀ j, raw34291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34291step0 = (fun i j => raw34291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34291step0 raw34291; decide +kernel
      have hl : raw34291step0Labels = raw34291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34291 raw34291Labels permutation346 hz
    mixedMoment B raw34291step0 raw34291step0Labels = mixedMoment B raw34291step1 raw34291step1Labels := by
      have ha : raw34291step1 = (fun i j => raw34291step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34291step1 raw34291step0; decide +kernel
      have hl : raw34291step1Labels = raw34291step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34291step0 raw34291step0Labels permutation34 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw34292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34292step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34292 raw34292Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw34292 raw34292Labels = mixedMoment B raw34292step0 raw34292step0Labels := by
      have hz : ∀ j, raw34292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34292step0 = (fun i j => raw34292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34292step0 raw34292; decide +kernel
      have hl : raw34292step0Labels = raw34292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34292 raw34292Labels permutation346 hz
    mixedMoment B raw34292step0 raw34292step0Labels = mixedMoment B raw34292step1 raw34292step1Labels := by
      have ha : raw34292step1 = (fun i j => raw34292step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34292step1 raw34292step0; decide +kernel
      have hl : raw34292step1Labels = raw34292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34292step0 raw34292step0Labels permutation34 permutation7
    mixedMoment B raw34292step1 raw34292step1Labels = mixedMoment B raw34292step2 raw34292step2Labels := by
      have ha : raw34292step2 = -raw34292step1 := by apply Matrix.ext; change ∀ i j, raw34292step2 i j = -(raw34292step1 i j); unfold raw34292step2 raw34292step1; decide +kernel
      have hl : raw34292step2Labels = raw34292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34292step2 raw34292step2Labels = mixedMoment B raw34292step3 raw34292step3Labels := by
      have ha : raw34292step3 = raw34292step2 := by apply Matrix.ext; unfold raw34292step3 raw34292step2; decide +kernel
      have hl : raw34292step2Labels = labelEmbedding10 ∘ raw34292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34292step2 raw34292step2Labels raw34292step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw34293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34293step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34293step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34293 raw34293Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw34293 raw34293Labels = mixedMoment B raw34293step0 raw34293step0Labels := by
      have ha : raw34293step0 = (fun i j => raw34293 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34293step0 raw34293; decide +kernel
      have hl : raw34293step0Labels = raw34293Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34293 raw34293Labels permutation154 permutation7
    mixedMoment B raw34293step0 raw34293step0Labels = mixedMoment B raw34293step1 raw34293step1Labels := by
      have ha : raw34293step1 = -raw34293step0 := by apply Matrix.ext; change ∀ i j, raw34293step1 i j = -(raw34293step0 i j); unfold raw34293step1 raw34293step0; decide +kernel
      have hl : raw34293step1Labels = raw34293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34293step1 raw34293step1Labels = mixedMoment B raw34293step2 raw34293step2Labels := by
      have ha : raw34293step2 = raw34293step1 := by apply Matrix.ext; unfold raw34293step2 raw34293step1; decide +kernel
      have hl : raw34293step1Labels = labelEmbedding10 ∘ raw34293step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34293step1 raw34293step1Labels raw34293step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw34294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34294step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34294 raw34294Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw34294 raw34294Labels = mixedMoment B raw34294step0 raw34294step0Labels := by
      have hz : ∀ j, raw34294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34294step0 = (fun i j => raw34294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34294step0 raw34294; decide +kernel
      have hl : raw34294step0Labels = raw34294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34294 raw34294Labels permutation346 hz
    mixedMoment B raw34294step0 raw34294step0Labels = mixedMoment B raw34294step1 raw34294step1Labels := by
      have ha : raw34294step1 = (fun i j => raw34294step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34294step1 raw34294step0; decide +kernel
      have hl : raw34294step1Labels = raw34294step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34294step0 raw34294step0Labels permutation34 permutation7
    mixedMoment B raw34294step1 raw34294step1Labels = mixedMoment B raw34294step2 raw34294step2Labels := by
      have ha : raw34294step2 = -raw34294step1 := by apply Matrix.ext; change ∀ i j, raw34294step2 i j = -(raw34294step1 i j); unfold raw34294step2 raw34294step1; decide +kernel
      have hl : raw34294step2Labels = raw34294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34294step2 raw34294step2Labels = mixedMoment B raw34294step3 raw34294step3Labels := by
      have ha : raw34294step3 = raw34294step2 := by apply Matrix.ext; unfold raw34294step3 raw34294step2; decide +kernel
      have hl : raw34294step2Labels = labelEmbedding10 ∘ raw34294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34294step2 raw34294step2Labels raw34294step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw34295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34295step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34295 raw34295Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw34295 raw34295Labels = mixedMoment B raw34295step0 raw34295step0Labels := by
      have hz : ∀ j, raw34295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34295step0 = (fun i j => raw34295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34295step0 raw34295; decide +kernel
      have hl : raw34295step0Labels = raw34295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34295 raw34295Labels permutation520 hz
    mixedMoment B raw34295step0 raw34295step0Labels = mixedMoment B raw34295step1 raw34295step1Labels := by
      have hz : ∀ j, raw34295step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34295step1 = (fun i j => raw34295step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34295step1 raw34295step0; decide +kernel
      have hl : raw34295step1Labels = raw34295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34295step0 raw34295step0Labels permutation80 hz
    mixedMoment B raw34295step1 raw34295step1Labels = mixedMoment B raw34295step2 raw34295step2Labels := by
      have ha : raw34295step2 = (fun i j => raw34295step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34295step2 raw34295step1; decide +kernel
      have hl : raw34295step2Labels = raw34295step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34295step1 raw34295step1Labels permutation8 permutation7
    mixedMoment B raw34295step2 raw34295step2Labels = mixedMoment B raw34295step3 raw34295step3Labels := by
      have ha : raw34295step3 = -raw34295step2 := by apply Matrix.ext; change ∀ i j, raw34295step3 i j = -(raw34295step2 i j); unfold raw34295step3 raw34295step2; decide +kernel
      have hl : raw34295step3Labels = raw34295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34295step3 raw34295step3Labels = mixedMoment B raw34295step4 raw34295step4Labels := by
      have ha : raw34295step4 = raw34295step3 := by apply Matrix.ext; unfold raw34295step4 raw34295step3; decide +kernel
      have hl : raw34295step3Labels = labelEmbedding10 ∘ raw34295step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34295step3 raw34295step3Labels raw34295step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw34296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34296step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34296 raw34296Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34296 raw34296Labels = mixedMoment B raw34296step0 raw34296step0Labels := by
      have hz : ∀ j, raw34296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34296step0 = (fun i j => raw34296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34296step0 raw34296; decide +kernel
      have hl : raw34296step0Labels = raw34296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34296 raw34296Labels permutation346 hz
    mixedMoment B raw34296step0 raw34296step0Labels = mixedMoment B raw34296step1 raw34296step1Labels := by
      have ha : raw34296step1 = (fun i j => raw34296step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34296step1 raw34296step0; decide +kernel
      have hl : raw34296step1Labels = raw34296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34296step0 raw34296step0Labels permutation34 permutation7
    mixedMoment B raw34296step1 raw34296step1Labels = mixedMoment B raw34296step2 raw34296step2Labels := by
      have ha : raw34296step2 = -raw34296step1 := by apply Matrix.ext; change ∀ i j, raw34296step2 i j = -(raw34296step1 i j); unfold raw34296step2 raw34296step1; decide +kernel
      have hl : raw34296step2Labels = raw34296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34296step2 raw34296step2Labels = mixedMoment B raw34296step3 raw34296step3Labels := by
      have ha : raw34296step3 = raw34296step2 := by apply Matrix.ext; unfold raw34296step3 raw34296step2; decide +kernel
      have hl : raw34296step2Labels = labelEmbedding10 ∘ raw34296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34296step2 raw34296step2Labels raw34296step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw34297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34297 raw34297Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw34297 raw34297Labels = mixedMoment B raw34297step0 raw34297step0Labels := by
      have hz : ∀ j, raw34297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34297step0 = (fun i j => raw34297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34297step0 raw34297; decide +kernel
      have hl : raw34297step0Labels = raw34297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34297 raw34297Labels permutation346 hz
    mixedMoment B raw34297step0 raw34297step0Labels = mixedMoment B raw34297step1 raw34297step1Labels := by
      have hz : ∀ j, raw34297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34297step1 = (fun i j => raw34297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34297step1 raw34297step0; decide +kernel
      have hl : raw34297step1Labels = raw34297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34297step0 raw34297step0Labels permutation56 hz
    mixedMoment B raw34297step1 raw34297step1Labels = mixedMoment B raw34297step2 raw34297step2Labels := by
      have ha : raw34297step2 = (fun i j => raw34297step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34297step2 raw34297step1; decide +kernel
      have hl : raw34297step2Labels = raw34297step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34297step1 raw34297step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw34298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34298 raw34298Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34298 raw34298Labels = mixedMoment B raw34298step0 raw34298step0Labels := by
      have ha : raw34298step0 = (fun i j => raw34298 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34298step0 raw34298; decide +kernel
      have hl : raw34298step0Labels = raw34298Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34298 raw34298Labels permutation154 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw34299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34299 raw34299Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34299 raw34299Labels = mixedMoment B raw34299step0 raw34299step0Labels := by
      have ha : raw34299step0 = (fun i j => raw34299 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34299step0 raw34299; decide +kernel
      have hl : raw34299step0Labels = raw34299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34299 raw34299Labels permutation158 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw34300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34300 raw34300Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34300 raw34300Labels = mixedMoment B raw34300step0 raw34300step0Labels := by
      have hz : ∀ j, raw34300 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34300step0 = (fun i j => raw34300 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34300step0 raw34300; decide +kernel
      have hl : raw34300step0Labels = raw34300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34300 raw34300Labels permutation520 hz
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34301 raw34301Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34301 raw34301Labels = mixedMoment B raw34301step0 raw34301step0Labels := by
      have ha : raw34301step0 = (fun i j => raw34301 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34301step0 raw34301; decide +kernel
      have hl : raw34301step0Labels = raw34301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34301 raw34301Labels permutation154 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34302 raw34302Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw34302 raw34302Labels = mixedMoment B raw34302step0 raw34302step0Labels := by
      have hz : ∀ j, raw34302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34302step0 = (fun i j => raw34302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34302step0 raw34302; decide +kernel
      have hl : raw34302step0Labels = raw34302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34302 raw34302Labels permutation346 hz
    mixedMoment B raw34302step0 raw34302step0Labels = mixedMoment B raw34302step1 raw34302step1Labels := by
      have ha : raw34302step1 = (fun i j => raw34302step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34302step1 raw34302step0; decide +kernel
      have hl : raw34302step1Labels = raw34302step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34302step0 raw34302step0Labels permutation34 permutation2
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw34303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34303 raw34303Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34303 raw34303Labels = mixedMoment B raw34303step0 raw34303step0Labels := by
      have ha : raw34303step0 = (fun i j => raw34303 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34303step0 raw34303; decide +kernel
      have hl : raw34303step0Labels = raw34303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34303 raw34303Labels permutation154 permutation2
    _ = mixedMoment B node4763 node4763Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
