import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32384 raw32384Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw32384 raw32384Labels = mixedMoment B raw32384step0 raw32384step0Labels := by
      have ha : raw32384step0 = (fun i j => raw32384 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32384step0 raw32384; decide +kernel
      have hl : raw32384step0Labels = raw32384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32384 raw32384Labels permutation688 permutation2
    mixedMoment B raw32384step0 raw32384step0Labels = mixedMoment B raw32384step1 raw32384step1Labels := by
      have ha : raw32384step1 = -raw32384step0 := by apply Matrix.ext; change ∀ i j, raw32384step1 i j = -(raw32384step0 i j); unfold raw32384step1 raw32384step0; decide +kernel
      have hl : raw32384step1Labels = raw32384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw32385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32385 raw32385Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw32385 raw32385Labels = mixedMoment B raw32385step0 raw32385step0Labels := by
      have hz : ∀ j, raw32385 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32385step0 = (fun i j => raw32385 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32385step0 raw32385; decide +kernel
      have hl : raw32385step0Labels = raw32385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32385 raw32385Labels permutation520 hz
    mixedMoment B raw32385step0 raw32385step0Labels = mixedMoment B raw32385step1 raw32385step1Labels := by
      have ha : raw32385step1 = (fun i j => raw32385step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32385step1 raw32385step0; decide +kernel
      have hl : raw32385step1Labels = raw32385step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32385step0 raw32385step0Labels permutation151 permutation2
    mixedMoment B raw32385step1 raw32385step1Labels = mixedMoment B raw32385step2 raw32385step2Labels := by
      have ha : raw32385step2 = -raw32385step1 := by apply Matrix.ext; change ∀ i j, raw32385step2 i j = -(raw32385step1 i j); unfold raw32385step2 raw32385step1; decide +kernel
      have hl : raw32385step2Labels = raw32385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw32386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32386 raw32386Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw32386 raw32386Labels = mixedMoment B raw32386step0 raw32386step0Labels := by
      have ha : raw32386step0 = (fun i j => raw32386 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32386step0 raw32386; decide +kernel
      have hl : raw32386step0Labels = raw32386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32386 raw32386Labels permutation154 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw32387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32387 raw32387Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw32387 raw32387Labels = mixedMoment B raw32387step0 raw32387step0Labels := by
      have ha : raw32387step0 = (fun i j => raw32387 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32387step0 raw32387; decide +kernel
      have hl : raw32387step0Labels = raw32387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32387 raw32387Labels permutation152 permutation3
    mixedMoment B raw32387step0 raw32387step0Labels = mixedMoment B raw32387step1 raw32387step1Labels := by
      have ha : raw32387step1 = raw32387step0 := by apply Matrix.ext; unfold raw32387step1 raw32387step0; decide +kernel
      have hl : raw32387step0Labels = labelEmbedding6 ∘ raw32387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32387step0 raw32387step0Labels raw32387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw32388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32388step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32388 raw32388Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32388 raw32388Labels = mixedMoment B raw32388step0 raw32388step0Labels := by
      have ha : raw32388step0 = (fun i j => raw32388 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32388step0 raw32388; decide +kernel
      have hl : raw32388step0Labels = raw32388Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32388 raw32388Labels permutation176 permutation3
    mixedMoment B raw32388step0 raw32388step0Labels = mixedMoment B raw32388step1 raw32388step1Labels := by
      have ha : raw32388step1 = raw32388step0 := by apply Matrix.ext; unfold raw32388step1 raw32388step0; decide +kernel
      have hl : raw32388step0Labels = labelEmbedding6 ∘ raw32388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32388step0 raw32388step0Labels raw32388step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32389 raw32389Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw32389 raw32389Labels = mixedMoment B raw32389step0 raw32389step0Labels := by
      have ha : raw32389step0 = (fun i j => raw32389 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32389step0 raw32389; decide +kernel
      have hl : raw32389step0Labels = raw32389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32389 raw32389Labels permutation200 permutation3
    mixedMoment B raw32389step0 raw32389step0Labels = mixedMoment B raw32389step1 raw32389step1Labels := by
      have ha : raw32389step1 = raw32389step0 := by apply Matrix.ext; unfold raw32389step1 raw32389step0; decide +kernel
      have hl : raw32389step0Labels = labelEmbedding6 ∘ raw32389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32389step0 raw32389step0Labels raw32389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw32390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32390step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32390 raw32390Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw32390 raw32390Labels = mixedMoment B raw32390step0 raw32390step0Labels := by
      have hz : ∀ j, raw32390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32390step0 = (fun i j => raw32390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32390step0 raw32390; decide +kernel
      have hl : raw32390step0Labels = raw32390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32390 raw32390Labels permutation520 hz
    mixedMoment B raw32390step0 raw32390step0Labels = mixedMoment B raw32390step1 raw32390step1Labels := by
      have ha : raw32390step1 = (fun i j => raw32390step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32390step1 raw32390step0; decide +kernel
      have hl : raw32390step1Labels = raw32390step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32390step0 raw32390step0Labels permutation32 permutation3
    mixedMoment B raw32390step1 raw32390step1Labels = mixedMoment B raw32390step2 raw32390step2Labels := by
      have ha : raw32390step2 = raw32390step1 := by apply Matrix.ext; unfold raw32390step2 raw32390step1; decide +kernel
      have hl : raw32390step1Labels = labelEmbedding6 ∘ raw32390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32390step1 raw32390step1Labels raw32390step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw32391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32391 raw32391Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw32391 raw32391Labels = mixedMoment B raw32391step0 raw32391step0Labels := by
      have ha : raw32391step0 = (fun i j => raw32391 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32391step0 raw32391; decide +kernel
      have hl : raw32391step0Labels = raw32391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32391 raw32391Labels permutation156 permutation3
    mixedMoment B raw32391step0 raw32391step0Labels = mixedMoment B raw32391step1 raw32391step1Labels := by
      have ha : raw32391step1 = raw32391step0 := by apply Matrix.ext; unfold raw32391step1 raw32391step0; decide +kernel
      have hl : raw32391step0Labels = labelEmbedding6 ∘ raw32391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32391step0 raw32391step0Labels raw32391step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw32392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32392 raw32392Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw32392 raw32392Labels = mixedMoment B raw32392step0 raw32392step0Labels := by
      have ha : raw32392step0 = (fun i j => raw32392 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32392step0 raw32392; decide +kernel
      have hl : raw32392step0Labels = raw32392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32392 raw32392Labels permutation160 permutation3
    mixedMoment B raw32392step0 raw32392step0Labels = mixedMoment B raw32392step1 raw32392step1Labels := by
      have ha : raw32392step1 = raw32392step0 := by apply Matrix.ext; unfold raw32392step1 raw32392step0; decide +kernel
      have hl : raw32392step0Labels = labelEmbedding6 ∘ raw32392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32392step0 raw32392step0Labels raw32392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw32393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32393 raw32393Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw32393 raw32393Labels = mixedMoment B raw32393step0 raw32393step0Labels := by
      have ha : raw32393step0 = (fun i j => raw32393 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32393step0 raw32393; decide +kernel
      have hl : raw32393step0Labels = raw32393Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32393 raw32393Labels permutation160 permutation3
    mixedMoment B raw32393step0 raw32393step0Labels = mixedMoment B raw32393step1 raw32393step1Labels := by
      have ha : raw32393step1 = raw32393step0 := by apply Matrix.ext; unfold raw32393step1 raw32393step0; decide +kernel
      have hl : raw32393step0Labels = labelEmbedding6 ∘ raw32393step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32393step0 raw32393step0Labels raw32393step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw32394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32394 raw32394Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32394 raw32394Labels = mixedMoment B raw32394step0 raw32394step0Labels := by
      have ha : raw32394step0 = (fun i j => raw32394 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32394step0 raw32394; decide +kernel
      have hl : raw32394step0Labels = raw32394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32394 raw32394Labels permutation160 permutation3
    mixedMoment B raw32394step0 raw32394step0Labels = mixedMoment B raw32394step1 raw32394step1Labels := by
      have ha : raw32394step1 = raw32394step0 := by apply Matrix.ext; unfold raw32394step1 raw32394step0; decide +kernel
      have hl : raw32394step0Labels = labelEmbedding6 ∘ raw32394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32394step0 raw32394step0Labels raw32394step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw32395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32395step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32395 raw32395Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32395 raw32395Labels = mixedMoment B raw32395step0 raw32395step0Labels := by
      have hz : ∀ j, raw32395 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32395step0 = (fun i j => raw32395 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32395step0 raw32395; decide +kernel
      have hl : raw32395step0Labels = raw32395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32395 raw32395Labels permutation520 hz
    mixedMoment B raw32395step0 raw32395step0Labels = mixedMoment B raw32395step1 raw32395step1Labels := by
      have ha : raw32395step1 = (fun i j => raw32395step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32395step1 raw32395step0; decide +kernel
      have hl : raw32395step1Labels = raw32395step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32395step0 raw32395step0Labels permutation34 permutation3
    mixedMoment B raw32395step1 raw32395step1Labels = mixedMoment B raw32395step2 raw32395step2Labels := by
      have ha : raw32395step2 = raw32395step1 := by apply Matrix.ext; unfold raw32395step2 raw32395step1; decide +kernel
      have hl : raw32395step1Labels = labelEmbedding6 ∘ raw32395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32395step1 raw32395step1Labels raw32395step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw32396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32396 raw32396Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw32396 raw32396Labels = mixedMoment B raw32396step0 raw32396step0Labels := by
      have ha : raw32396step0 = (fun i j => raw32396 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32396step0 raw32396; decide +kernel
      have hl : raw32396step0Labels = raw32396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32396 raw32396Labels permutation173 permutation3
    mixedMoment B raw32396step0 raw32396step0Labels = mixedMoment B raw32396step1 raw32396step1Labels := by
      have ha : raw32396step1 = raw32396step0 := by apply Matrix.ext; unfold raw32396step1 raw32396step0; decide +kernel
      have hl : raw32396step0Labels = labelEmbedding6 ∘ raw32396step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32396step0 raw32396step0Labels raw32396step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw32397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32397step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32397 raw32397Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw32397 raw32397Labels = mixedMoment B raw32397step0 raw32397step0Labels := by
      have ha : raw32397step0 = (fun i j => raw32397 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32397step0 raw32397; decide +kernel
      have hl : raw32397step0Labels = raw32397Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32397 raw32397Labels permutation155 permutation3
    mixedMoment B raw32397step0 raw32397step0Labels = mixedMoment B raw32397step1 raw32397step1Labels := by
      have ha : raw32397step1 = raw32397step0 := by apply Matrix.ext; unfold raw32397step1 raw32397step0; decide +kernel
      have hl : raw32397step0Labels = labelEmbedding6 ∘ raw32397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32397step0 raw32397step0Labels raw32397step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw32398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32398 raw32398Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw32398 raw32398Labels = mixedMoment B raw32398step0 raw32398step0Labels := by
      have ha : raw32398step0 = (fun i j => raw32398 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32398step0 raw32398; decide +kernel
      have hl : raw32398step0Labels = raw32398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32398 raw32398Labels permutation155 permutation3
    mixedMoment B raw32398step0 raw32398step0Labels = mixedMoment B raw32398step1 raw32398step1Labels := by
      have ha : raw32398step1 = raw32398step0 := by apply Matrix.ext; unfold raw32398step1 raw32398step0; decide +kernel
      have hl : raw32398step0Labels = labelEmbedding6 ∘ raw32398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32398step0 raw32398step0Labels raw32398step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw32399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32399 raw32399Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw32399 raw32399Labels = mixedMoment B raw32399step0 raw32399step0Labels := by
      have ha : raw32399step0 = (fun i j => raw32399 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32399step0 raw32399; decide +kernel
      have hl : raw32399step0Labels = raw32399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32399 raw32399Labels permutation155 permutation3
    mixedMoment B raw32399step0 raw32399step0Labels = mixedMoment B raw32399step1 raw32399step1Labels := by
      have ha : raw32399step1 = raw32399step0 := by apply Matrix.ext; unfold raw32399step1 raw32399step0; decide +kernel
      have hl : raw32399step0Labels = labelEmbedding6 ∘ raw32399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32399step0 raw32399step0Labels raw32399step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw32400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32400 raw32400Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32400 raw32400Labels = mixedMoment B raw32400step0 raw32400step0Labels := by
      have hz : ∀ j, raw32400 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32400step0 = (fun i j => raw32400 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32400step0 raw32400; decide +kernel
      have hl : raw32400step0Labels = raw32400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32400 raw32400Labels permutation520 hz
    mixedMoment B raw32400step0 raw32400step0Labels = mixedMoment B raw32400step1 raw32400step1Labels := by
      have ha : raw32400step1 = (fun i j => raw32400step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32400step1 raw32400step0; decide +kernel
      have hl : raw32400step1Labels = raw32400step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32400step0 raw32400step0Labels permutation33 permutation3
    mixedMoment B raw32400step1 raw32400step1Labels = mixedMoment B raw32400step2 raw32400step2Labels := by
      have ha : raw32400step2 = raw32400step1 := by apply Matrix.ext; unfold raw32400step2 raw32400step1; decide +kernel
      have hl : raw32400step1Labels = labelEmbedding6 ∘ raw32400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32400step1 raw32400step1Labels raw32400step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32401 raw32401Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw32401 raw32401Labels = mixedMoment B raw32401step0 raw32401step0Labels := by
      have ha : raw32401step0 = (fun i j => raw32401 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32401step0 raw32401; decide +kernel
      have hl : raw32401step0Labels = raw32401Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32401 raw32401Labels permutation157 permutation3
    mixedMoment B raw32401step0 raw32401step0Labels = mixedMoment B raw32401step1 raw32401step1Labels := by
      have ha : raw32401step1 = raw32401step0 := by apply Matrix.ext; unfold raw32401step1 raw32401step0; decide +kernel
      have hl : raw32401step0Labels = labelEmbedding6 ∘ raw32401step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32401step0 raw32401step0Labels raw32401step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw32402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32402 raw32402Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw32402 raw32402Labels = mixedMoment B raw32402step0 raw32402step0Labels := by
      have ha : raw32402step0 = (fun i j => raw32402 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32402step0 raw32402; decide +kernel
      have hl : raw32402step0Labels = raw32402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32402 raw32402Labels permutation153 permutation3
    mixedMoment B raw32402step0 raw32402step0Labels = mixedMoment B raw32402step1 raw32402step1Labels := by
      have ha : raw32402step1 = raw32402step0 := by apply Matrix.ext; unfold raw32402step1 raw32402step0; decide +kernel
      have hl : raw32402step0Labels = labelEmbedding6 ∘ raw32402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32402step0 raw32402step0Labels raw32402step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw32403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32403step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32403 raw32403Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw32403 raw32403Labels = mixedMoment B raw32403step0 raw32403step0Labels := by
      have ha : raw32403step0 = (fun i j => raw32403 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32403step0 raw32403; decide +kernel
      have hl : raw32403step0Labels = raw32403Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32403 raw32403Labels permutation153 permutation3
    mixedMoment B raw32403step0 raw32403step0Labels = mixedMoment B raw32403step1 raw32403step1Labels := by
      have ha : raw32403step1 = raw32403step0 := by apply Matrix.ext; unfold raw32403step1 raw32403step0; decide +kernel
      have hl : raw32403step0Labels = labelEmbedding6 ∘ raw32403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32403step0 raw32403step0Labels raw32403step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw32404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32404step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32404 raw32404Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw32404 raw32404Labels = mixedMoment B raw32404step0 raw32404step0Labels := by
      have ha : raw32404step0 = (fun i j => raw32404 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32404step0 raw32404; decide +kernel
      have hl : raw32404step0Labels = raw32404Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32404 raw32404Labels permutation153 permutation3
    mixedMoment B raw32404step0 raw32404step0Labels = mixedMoment B raw32404step1 raw32404step1Labels := by
      have ha : raw32404step1 = raw32404step0 := by apply Matrix.ext; unfold raw32404step1 raw32404step0; decide +kernel
      have hl : raw32404step0Labels = labelEmbedding6 ∘ raw32404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32404step0 raw32404step0Labels raw32404step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw32405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32405 raw32405Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw32405 raw32405Labels = mixedMoment B raw32405step0 raw32405step0Labels := by
      have ha : raw32405step0 = (fun i j => raw32405 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32405step0 raw32405; decide +kernel
      have hl : raw32405step0Labels = raw32405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32405 raw32405Labels permutation159 permutation3
    mixedMoment B raw32405step0 raw32405step0Labels = mixedMoment B raw32405step1 raw32405step1Labels := by
      have ha : raw32405step1 = raw32405step0 := by apply Matrix.ext; unfold raw32405step1 raw32405step0; decide +kernel
      have hl : raw32405step0Labels = labelEmbedding6 ∘ raw32405step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32405step0 raw32405step0Labels raw32405step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw32406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32406step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32406 raw32406Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw32406 raw32406Labels = mixedMoment B raw32406step0 raw32406step0Labels := by
      have ha : raw32406step0 = (fun i j => raw32406 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32406step0 raw32406; decide +kernel
      have hl : raw32406step0Labels = raw32406Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32406 raw32406Labels permutation156 permutation3
    mixedMoment B raw32406step0 raw32406step0Labels = mixedMoment B raw32406step1 raw32406step1Labels := by
      have ha : raw32406step1 = raw32406step0 := by apply Matrix.ext; unfold raw32406step1 raw32406step0; decide +kernel
      have hl : raw32406step0Labels = labelEmbedding6 ∘ raw32406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32406step0 raw32406step0Labels raw32406step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw32407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32407step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32407 raw32407Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw32407 raw32407Labels = mixedMoment B raw32407step0 raw32407step0Labels := by
      have ha : raw32407step0 = (fun i j => raw32407 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32407step0 raw32407; decide +kernel
      have hl : raw32407step0Labels = raw32407Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32407 raw32407Labels permutation152 permutation3
    mixedMoment B raw32407step0 raw32407step0Labels = mixedMoment B raw32407step1 raw32407step1Labels := by
      have ha : raw32407step1 = raw32407step0 := by apply Matrix.ext; unfold raw32407step1 raw32407step0; decide +kernel
      have hl : raw32407step0Labels = labelEmbedding6 ∘ raw32407step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32407step0 raw32407step0Labels raw32407step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw32408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32408step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32408 raw32408Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw32408 raw32408Labels = mixedMoment B raw32408step0 raw32408step0Labels := by
      have ha : raw32408step0 = (fun i j => raw32408 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32408step0 raw32408; decide +kernel
      have hl : raw32408step0Labels = raw32408Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32408 raw32408Labels permutation152 permutation3
    mixedMoment B raw32408step0 raw32408step0Labels = mixedMoment B raw32408step1 raw32408step1Labels := by
      have ha : raw32408step1 = raw32408step0 := by apply Matrix.ext; unfold raw32408step1 raw32408step0; decide +kernel
      have hl : raw32408step0Labels = labelEmbedding6 ∘ raw32408step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32408step0 raw32408step0Labels raw32408step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw32409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32409 raw32409Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw32409 raw32409Labels = mixedMoment B raw32409step0 raw32409step0Labels := by
      have ha : raw32409step0 = (fun i j => raw32409 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32409step0 raw32409; decide +kernel
      have hl : raw32409step0Labels = raw32409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32409 raw32409Labels permutation662 permutation2
    mixedMoment B raw32409step0 raw32409step0Labels = mixedMoment B raw32409step1 raw32409step1Labels := by
      have ha : raw32409step1 = -raw32409step0 := by apply Matrix.ext; change ∀ i j, raw32409step1 i j = -(raw32409step0 i j); unfold raw32409step1 raw32409step0; decide +kernel
      have hl : raw32409step1Labels = raw32409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw32410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32410 raw32410Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw32410 raw32410Labels = mixedMoment B raw32410step0 raw32410step0Labels := by
      have ha : raw32410step0 = (fun i j => raw32410 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32410step0 raw32410; decide +kernel
      have hl : raw32410step0Labels = raw32410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32410 raw32410Labels permutation688 permutation2
    mixedMoment B raw32410step0 raw32410step0Labels = mixedMoment B raw32410step1 raw32410step1Labels := by
      have ha : raw32410step1 = -raw32410step0 := by apply Matrix.ext; change ∀ i j, raw32410step1 i j = -(raw32410step0 i j); unfold raw32410step1 raw32410step0; decide +kernel
      have hl : raw32410step1Labels = raw32410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw32411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32411 raw32411Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw32411 raw32411Labels = mixedMoment B raw32411step0 raw32411step0Labels := by
      have hz : ∀ j, raw32411 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32411step0 = (fun i j => raw32411 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32411step0 raw32411; decide +kernel
      have hl : raw32411step0Labels = raw32411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32411 raw32411Labels permutation520 hz
    mixedMoment B raw32411step0 raw32411step0Labels = mixedMoment B raw32411step1 raw32411step1Labels := by
      have ha : raw32411step1 = (fun i j => raw32411step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32411step1 raw32411step0; decide +kernel
      have hl : raw32411step1Labels = raw32411step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32411step0 raw32411step0Labels permutation151 permutation2
    mixedMoment B raw32411step1 raw32411step1Labels = mixedMoment B raw32411step2 raw32411step2Labels := by
      have ha : raw32411step2 = -raw32411step1 := by apply Matrix.ext; change ∀ i j, raw32411step2 i j = -(raw32411step1 i j); unfold raw32411step2 raw32411step1; decide +kernel
      have hl : raw32411step2Labels = raw32411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw32412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32412 raw32412Labels = mixedMoment B node3925 node3925Labels := by
  calc
    mixedMoment B raw32412 raw32412Labels = mixedMoment B raw32412step0 raw32412step0Labels := by
      have ha : raw32412step0 = (fun i j => raw32412 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32412step0 raw32412; decide +kernel
      have hl : raw32412step0Labels = raw32412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32412 raw32412Labels permutation152 permutation3
    _ = mixedMoment B node3925 node3925Labels := by rfl

def raw32413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32413 raw32413Labels = mixedMoment B node3988 node3988Labels := by
  calc
    mixedMoment B raw32413 raw32413Labels = mixedMoment B raw32413step0 raw32413step0Labels := by
      have ha : raw32413step0 = (fun i j => raw32413 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32413step0 raw32413; decide +kernel
      have hl : raw32413step0Labels = raw32413Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32413 raw32413Labels permutation152 permutation3
    _ = mixedMoment B node3988 node3988Labels := by rfl

def raw32414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32414 raw32414Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw32414 raw32414Labels = mixedMoment B raw32414step0 raw32414step0Labels := by
      have ha : raw32414step0 = (fun i j => raw32414 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32414step0 raw32414; decide +kernel
      have hl : raw32414step0Labels = raw32414Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32414 raw32414Labels permutation158 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw32415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32415 raw32415Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw32415 raw32415Labels = mixedMoment B raw32415step0 raw32415step0Labels := by
      have hz : ∀ j, raw32415 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32415step0 = (fun i j => raw32415 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32415step0 raw32415; decide +kernel
      have hl : raw32415step0Labels = raw32415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32415 raw32415Labels permutation520 hz
    mixedMoment B raw32415step0 raw32415step0Labels = mixedMoment B raw32415step1 raw32415step1Labels := by
      have ha : raw32415step1 = (fun i j => raw32415step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32415step1 raw32415step0; decide +kernel
      have hl : raw32415step1Labels = raw32415step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32415step0 raw32415step0Labels permutation32 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw32416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32416 raw32416Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw32416 raw32416Labels = mixedMoment B raw32416step0 raw32416step0Labels := by
      have ha : raw32416step0 = (fun i j => raw32416 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32416step0 raw32416; decide +kernel
      have hl : raw32416step0Labels = raw32416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32416 raw32416Labels permutation156 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw32417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32417 raw32417Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw32417 raw32417Labels = mixedMoment B raw32417step0 raw32417step0Labels := by
      have ha : raw32417step0 = (fun i j => raw32417 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32417step0 raw32417; decide +kernel
      have hl : raw32417step0Labels = raw32417Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32417 raw32417Labels permutation152 permutation3
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw32418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32418 raw32418Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw32418 raw32418Labels = mixedMoment B raw32418step0 raw32418step0Labels := by
      have ha : raw32418step0 = (fun i j => raw32418 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32418step0 raw32418; decide +kernel
      have hl : raw32418step0Labels = raw32418Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32418 raw32418Labels permutation176 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw32419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32419 raw32419Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw32419 raw32419Labels = mixedMoment B raw32419step0 raw32419step0Labels := by
      have ha : raw32419step0 = (fun i j => raw32419 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32419step0 raw32419; decide +kernel
      have hl : raw32419step0Labels = raw32419Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32419 raw32419Labels permutation200 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw32420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32420 raw32420Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw32420 raw32420Labels = mixedMoment B raw32420step0 raw32420step0Labels := by
      have hz : ∀ j, raw32420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32420step0 = (fun i j => raw32420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32420step0 raw32420; decide +kernel
      have hl : raw32420step0Labels = raw32420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32420 raw32420Labels permutation520 hz
    mixedMoment B raw32420step0 raw32420step0Labels = mixedMoment B raw32420step1 raw32420step1Labels := by
      have ha : raw32420step1 = (fun i j => raw32420step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32420step1 raw32420step0; decide +kernel
      have hl : raw32420step1Labels = raw32420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32420step0 raw32420step0Labels permutation32 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw32421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32421 raw32421Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw32421 raw32421Labels = mixedMoment B raw32421step0 raw32421step0Labels := by
      have ha : raw32421step0 = (fun i j => raw32421 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32421step0 raw32421; decide +kernel
      have hl : raw32421step0Labels = raw32421Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32421 raw32421Labels permutation156 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw32422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32422 raw32422Labels = mixedMoment B node923 node923Labels := by
  calc
    mixedMoment B raw32422 raw32422Labels = mixedMoment B raw32422step0 raw32422step0Labels := by
      have ha : raw32422step0 = (fun i j => raw32422 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32422step0 raw32422; decide +kernel
      have hl : raw32422step0Labels = raw32422Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32422 raw32422Labels permutation160 permutation3
    _ = mixedMoment B node923 node923Labels := by rfl

def raw32423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32423 raw32423Labels = mixedMoment B node2333 node2333Labels := by
  calc
    mixedMoment B raw32423 raw32423Labels = mixedMoment B raw32423step0 raw32423step0Labels := by
      have ha : raw32423step0 = (fun i j => raw32423 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32423step0 raw32423; decide +kernel
      have hl : raw32423step0Labels = raw32423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32423 raw32423Labels permutation160 permutation3
    _ = mixedMoment B node2333 node2333Labels := by rfl

def raw32424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32424 raw32424Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw32424 raw32424Labels = mixedMoment B raw32424step0 raw32424step0Labels := by
      have ha : raw32424step0 = (fun i j => raw32424 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32424step0 raw32424; decide +kernel
      have hl : raw32424step0Labels = raw32424Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32424 raw32424Labels permutation160 permutation3
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw32425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32425 raw32425Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw32425 raw32425Labels = mixedMoment B raw32425step0 raw32425step0Labels := by
      have hz : ∀ j, raw32425 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32425step0 = (fun i j => raw32425 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32425step0 raw32425; decide +kernel
      have hl : raw32425step0Labels = raw32425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32425 raw32425Labels permutation520 hz
    mixedMoment B raw32425step0 raw32425step0Labels = mixedMoment B raw32425step1 raw32425step1Labels := by
      have ha : raw32425step1 = (fun i j => raw32425step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32425step1 raw32425step0; decide +kernel
      have hl : raw32425step1Labels = raw32425step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32425step0 raw32425step0Labels permutation34 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw32426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32426 raw32426Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw32426 raw32426Labels = mixedMoment B raw32426step0 raw32426step0Labels := by
      have ha : raw32426step0 = (fun i j => raw32426 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32426step0 raw32426; decide +kernel
      have hl : raw32426step0Labels = raw32426Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32426 raw32426Labels permutation173 permutation3
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw32427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32427 raw32427Labels = mixedMoment B node910 node910Labels := by
  calc
    mixedMoment B raw32427 raw32427Labels = mixedMoment B raw32427step0 raw32427step0Labels := by
      have ha : raw32427step0 = (fun i j => raw32427 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32427step0 raw32427; decide +kernel
      have hl : raw32427step0Labels = raw32427Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32427 raw32427Labels permutation155 permutation3
    _ = mixedMoment B node910 node910Labels := by rfl

def raw32428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32428 raw32428Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw32428 raw32428Labels = mixedMoment B raw32428step0 raw32428step0Labels := by
      have ha : raw32428step0 = (fun i j => raw32428 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32428step0 raw32428; decide +kernel
      have hl : raw32428step0Labels = raw32428Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32428 raw32428Labels permutation155 permutation3
    _ = mixedMoment B node2324 node2324Labels := by rfl

def raw32429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32429 raw32429Labels = mixedMoment B node2530 node2530Labels := by
  calc
    mixedMoment B raw32429 raw32429Labels = mixedMoment B raw32429step0 raw32429step0Labels := by
      have ha : raw32429step0 = (fun i j => raw32429 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32429step0 raw32429; decide +kernel
      have hl : raw32429step0Labels = raw32429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32429 raw32429Labels permutation155 permutation3
    _ = mixedMoment B node2530 node2530Labels := by rfl

def raw32430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32430step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32430 raw32430Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw32430 raw32430Labels = mixedMoment B raw32430step0 raw32430step0Labels := by
      have hz : ∀ j, raw32430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32430step0 = (fun i j => raw32430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32430step0 raw32430; decide +kernel
      have hl : raw32430step0Labels = raw32430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32430 raw32430Labels permutation520 hz
    mixedMoment B raw32430step0 raw32430step0Labels = mixedMoment B raw32430step1 raw32430step1Labels := by
      have ha : raw32430step1 = (fun i j => raw32430step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32430step1 raw32430step0; decide +kernel
      have hl : raw32430step1Labels = raw32430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32430step0 raw32430step0Labels permutation33 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw32431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32431 raw32431Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw32431 raw32431Labels = mixedMoment B raw32431step0 raw32431step0Labels := by
      have ha : raw32431step0 = (fun i j => raw32431 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32431step0 raw32431; decide +kernel
      have hl : raw32431step0Labels = raw32431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32431 raw32431Labels permutation157 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw32432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32432 raw32432Labels = mixedMoment B node906 node906Labels := by
  calc
    mixedMoment B raw32432 raw32432Labels = mixedMoment B raw32432step0 raw32432step0Labels := by
      have ha : raw32432step0 = (fun i j => raw32432 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32432step0 raw32432; decide +kernel
      have hl : raw32432step0Labels = raw32432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32432 raw32432Labels permutation153 permutation3
    _ = mixedMoment B node906 node906Labels := by rfl

def raw32433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32433 raw32433Labels = mixedMoment B node2321 node2321Labels := by
  calc
    mixedMoment B raw32433 raw32433Labels = mixedMoment B raw32433step0 raw32433step0Labels := by
      have ha : raw32433step0 = (fun i j => raw32433 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32433step0 raw32433; decide +kernel
      have hl : raw32433step0Labels = raw32433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32433 raw32433Labels permutation153 permutation3
    _ = mixedMoment B node2321 node2321Labels := by rfl

def raw32434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32434 raw32434Labels = mixedMoment B node2527 node2527Labels := by
  calc
    mixedMoment B raw32434 raw32434Labels = mixedMoment B raw32434step0 raw32434step0Labels := by
      have ha : raw32434step0 = (fun i j => raw32434 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32434step0 raw32434; decide +kernel
      have hl : raw32434step0Labels = raw32434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32434 raw32434Labels permutation153 permutation3
    _ = mixedMoment B node2527 node2527Labels := by rfl

def raw32435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32435 raw32435Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw32435 raw32435Labels = mixedMoment B raw32435step0 raw32435step0Labels := by
      have ha : raw32435step0 = (fun i j => raw32435 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32435step0 raw32435; decide +kernel
      have hl : raw32435step0Labels = raw32435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32435 raw32435Labels permutation159 permutation3
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw32436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32436 raw32436Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw32436 raw32436Labels = mixedMoment B raw32436step0 raw32436step0Labels := by
      have ha : raw32436step0 = (fun i j => raw32436 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32436step0 raw32436; decide +kernel
      have hl : raw32436step0Labels = raw32436Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32436 raw32436Labels permutation156 permutation3
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw32437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32437 raw32437Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw32437 raw32437Labels = mixedMoment B raw32437step0 raw32437step0Labels := by
      have ha : raw32437step0 = (fun i j => raw32437 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32437step0 raw32437; decide +kernel
      have hl : raw32437step0Labels = raw32437Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32437 raw32437Labels permutation152 permutation3
    _ = mixedMoment B node905 node905Labels := by rfl

def raw32438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32438 raw32438Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw32438 raw32438Labels = mixedMoment B raw32438step0 raw32438step0Labels := by
      have ha : raw32438step0 = (fun i j => raw32438 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32438step0 raw32438; decide +kernel
      have hl : raw32438step0Labels = raw32438Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32438 raw32438Labels permutation152 permutation3
    _ = mixedMoment B node2320 node2320Labels := by rfl

def raw32439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32439 raw32439Labels = mixedMoment B node2526 node2526Labels := by
  calc
    mixedMoment B raw32439 raw32439Labels = mixedMoment B raw32439step0 raw32439step0Labels := by
      have ha : raw32439step0 = (fun i j => raw32439 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32439step0 raw32439; decide +kernel
      have hl : raw32439step0Labels = raw32439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32439 raw32439Labels permutation152 permutation3
    _ = mixedMoment B node2526 node2526Labels := by rfl

def raw32440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32440 raw32440Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw32440 raw32440Labels = mixedMoment B raw32440step0 raw32440step0Labels := by
      have ha : raw32440step0 = (fun i j => raw32440 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32440step0 raw32440; decide +kernel
      have hl : raw32440step0Labels = raw32440Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32440 raw32440Labels permutation158 permutation3
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw32441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32441step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32441 raw32441Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw32441 raw32441Labels = mixedMoment B raw32441step0 raw32441step0Labels := by
      have hz : ∀ j, raw32441 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32441step0 = (fun i j => raw32441 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32441step0 raw32441; decide +kernel
      have hl : raw32441step0Labels = raw32441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32441 raw32441Labels permutation520 hz
    mixedMoment B raw32441step0 raw32441step0Labels = mixedMoment B raw32441step1 raw32441step1Labels := by
      have ha : raw32441step1 = (fun i j => raw32441step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32441step1 raw32441step0; decide +kernel
      have hl : raw32441step1Labels = raw32441step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32441step0 raw32441step0Labels permutation32 permutation3
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw32442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32442 raw32442Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw32442 raw32442Labels = mixedMoment B raw32442step0 raw32442step0Labels := by
      have ha : raw32442step0 = (fun i j => raw32442 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32442step0 raw32442; decide +kernel
      have hl : raw32442step0Labels = raw32442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32442 raw32442Labels permutation663 permutation7
    mixedMoment B raw32442step0 raw32442step0Labels = mixedMoment B raw32442step1 raw32442step1Labels := by
      have ha : raw32442step1 = raw32442step0 := by apply Matrix.ext; unfold raw32442step1 raw32442step0; decide +kernel
      have hl : raw32442step0Labels = labelEmbedding1 ∘ raw32442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32442step0 raw32442step0Labels raw32442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw32443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32443step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32443 raw32443Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw32443 raw32443Labels = mixedMoment B raw32443step0 raw32443step0Labels := by
      have ha : raw32443step0 = (fun i j => raw32443 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32443step0 raw32443; decide +kernel
      have hl : raw32443step0Labels = raw32443Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32443 raw32443Labels permutation662 permutation7
    mixedMoment B raw32443step0 raw32443step0Labels = mixedMoment B raw32443step1 raw32443step1Labels := by
      have ha : raw32443step1 = raw32443step0 := by apply Matrix.ext; unfold raw32443step1 raw32443step0; decide +kernel
      have hl : raw32443step0Labels = labelEmbedding1 ∘ raw32443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32443step0 raw32443step0Labels raw32443step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

def raw32444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32444 raw32444Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32444 raw32444Labels = mixedMoment B raw32444step0 raw32444step0Labels := by
      have ha : raw32444step0 = (fun i j => raw32444 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32444step0 raw32444; decide +kernel
      have hl : raw32444step0Labels = raw32444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32444 raw32444Labels permutation664 permutation7
    mixedMoment B raw32444step0 raw32444step0Labels = mixedMoment B raw32444step1 raw32444step1Labels := by
      have ha : raw32444step1 = raw32444step0 := by apply Matrix.ext; unfold raw32444step1 raw32444step0; decide +kernel
      have hl : raw32444step0Labels = labelEmbedding1 ∘ raw32444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32444step0 raw32444step0Labels raw32444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw32445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32445 raw32445Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32445 raw32445Labels = mixedMoment B raw32445step0 raw32445step0Labels := by
      have hz : ∀ j, raw32445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32445step0 = (fun i j => raw32445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32445step0 raw32445; decide +kernel
      have hl : raw32445step0Labels = raw32445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32445 raw32445Labels permutation520 hz
    mixedMoment B raw32445step0 raw32445step0Labels = mixedMoment B raw32445step1 raw32445step1Labels := by
      have ha : raw32445step1 = (fun i j => raw32445step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32445step1 raw32445step0; decide +kernel
      have hl : raw32445step1Labels = raw32445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32445step0 raw32445step0Labels permutation151 permutation7
    mixedMoment B raw32445step1 raw32445step1Labels = mixedMoment B raw32445step2 raw32445step2Labels := by
      have ha : raw32445step2 = raw32445step1 := by apply Matrix.ext; unfold raw32445step2 raw32445step1; decide +kernel
      have hl : raw32445step1Labels = labelEmbedding1 ∘ raw32445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32445step1 raw32445step1Labels raw32445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw32446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32446 raw32446Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw32446 raw32446Labels = mixedMoment B raw32446step0 raw32446step0Labels := by
      have ha : raw32446step0 = (fun i j => raw32446 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32446step0 raw32446; decide +kernel
      have hl : raw32446step0Labels = raw32446Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32446 raw32446Labels permutation664 permutation7
    mixedMoment B raw32446step0 raw32446step0Labels = mixedMoment B raw32446step1 raw32446step1Labels := by
      have ha : raw32446step1 = raw32446step0 := by apply Matrix.ext; unfold raw32446step1 raw32446step0; decide +kernel
      have hl : raw32446step0Labels = labelEmbedding1 ∘ raw32446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32446step0 raw32446step0Labels raw32446step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw32447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32447step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32447 raw32447Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw32447 raw32447Labels = mixedMoment B raw32447step0 raw32447step0Labels := by
      have ha : raw32447step0 = (fun i j => raw32447 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32447step0 raw32447; decide +kernel
      have hl : raw32447step0Labels = raw32447Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32447 raw32447Labels permutation218 permutation5
    mixedMoment B raw32447step0 raw32447step0Labels = mixedMoment B raw32447step1 raw32447step1Labels := by
      have ha : raw32447step1 = -raw32447step0 := by apply Matrix.ext; change ∀ i j, raw32447step1 i j = -(raw32447step0 i j); unfold raw32447step1 raw32447step0; decide +kernel
      have hl : raw32447step1Labels = raw32447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32447step1 raw32447step1Labels = mixedMoment B raw32447step2 raw32447step2Labels := by
      have ha : raw32447step2 = raw32447step1 := by apply Matrix.ext; unfold raw32447step2 raw32447step1; decide +kernel
      have hl : raw32447step1Labels = labelEmbedding1 ∘ raw32447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32447step1 raw32447step1Labels raw32447step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw32448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw32448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32448 raw32448Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw32448 raw32448Labels = mixedMoment B raw32448step0 raw32448step0Labels := by
      have ha : raw32448step0 = (fun i j => raw32448 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32448step0 raw32448; decide +kernel
      have hl : raw32448step0Labels = raw32448Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32448 raw32448Labels permutation186 permutation5
    mixedMoment B raw32448step0 raw32448step0Labels = mixedMoment B raw32448step1 raw32448step1Labels := by
      have ha : raw32448step1 = -raw32448step0 := by apply Matrix.ext; change ∀ i j, raw32448step1 i j = -(raw32448step0 i j); unfold raw32448step1 raw32448step0; decide +kernel
      have hl : raw32448step1Labels = raw32448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32448step1 raw32448step1Labels = mixedMoment B raw32448step2 raw32448step2Labels := by
      have ha : raw32448step2 = raw32448step1 := by apply Matrix.ext; unfold raw32448step2 raw32448step1; decide +kernel
      have hl : raw32448step1Labels = labelEmbedding1 ∘ raw32448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32448step1 raw32448step1Labels raw32448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw32449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32449 raw32449Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw32449 raw32449Labels = mixedMoment B raw32449step0 raw32449step0Labels := by
      have ha : raw32449step0 = (fun i j => raw32449 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32449step0 raw32449; decide +kernel
      have hl : raw32449step0Labels = raw32449Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32449 raw32449Labels permutation218 permutation5
    mixedMoment B raw32449step0 raw32449step0Labels = mixedMoment B raw32449step1 raw32449step1Labels := by
      have ha : raw32449step1 = -raw32449step0 := by apply Matrix.ext; change ∀ i j, raw32449step1 i j = -(raw32449step0 i j); unfold raw32449step1 raw32449step0; decide +kernel
      have hl : raw32449step1Labels = raw32449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32449step1 raw32449step1Labels = mixedMoment B raw32449step2 raw32449step2Labels := by
      have ha : raw32449step2 = raw32449step1 := by apply Matrix.ext; unfold raw32449step2 raw32449step1; decide +kernel
      have hl : raw32449step1Labels = labelEmbedding1 ∘ raw32449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32449step1 raw32449step1Labels raw32449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw32450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw32450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32450 raw32450Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw32450 raw32450Labels = mixedMoment B raw32450step0 raw32450step0Labels := by
      have hz : ∀ j, raw32450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32450step0 = (fun i j => raw32450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32450step0 raw32450; decide +kernel
      have hl : raw32450step0Labels = raw32450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32450 raw32450Labels permutation520 hz
    mixedMoment B raw32450step0 raw32450step0Labels = mixedMoment B raw32450step1 raw32450step1Labels := by
      have ha : raw32450step1 = (fun i j => raw32450step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32450step1 raw32450step0; decide +kernel
      have hl : raw32450step1Labels = raw32450step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32450step0 raw32450step0Labels permutation48 permutation5
    mixedMoment B raw32450step1 raw32450step1Labels = mixedMoment B raw32450step2 raw32450step2Labels := by
      have ha : raw32450step2 = -raw32450step1 := by apply Matrix.ext; change ∀ i j, raw32450step2 i j = -(raw32450step1 i j); unfold raw32450step2 raw32450step1; decide +kernel
      have hl : raw32450step2Labels = raw32450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32450step2 raw32450step2Labels = mixedMoment B raw32450step3 raw32450step3Labels := by
      have ha : raw32450step3 = raw32450step2 := by apply Matrix.ext; unfold raw32450step3 raw32450step2; decide +kernel
      have hl : raw32450step2Labels = labelEmbedding1 ∘ raw32450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32450step2 raw32450step2Labels raw32450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw32451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw32451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32451step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32451 raw32451Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw32451 raw32451Labels = mixedMoment B raw32451step0 raw32451step0Labels := by
      have ha : raw32451step0 = (fun i j => raw32451 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32451step0 raw32451; decide +kernel
      have hl : raw32451step0Labels = raw32451Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32451 raw32451Labels permutation257 permutation5
    mixedMoment B raw32451step0 raw32451step0Labels = mixedMoment B raw32451step1 raw32451step1Labels := by
      have ha : raw32451step1 = -raw32451step0 := by apply Matrix.ext; change ∀ i j, raw32451step1 i j = -(raw32451step0 i j); unfold raw32451step1 raw32451step0; decide +kernel
      have hl : raw32451step1Labels = raw32451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32451step1 raw32451step1Labels = mixedMoment B raw32451step2 raw32451step2Labels := by
      have ha : raw32451step2 = raw32451step1 := by apply Matrix.ext; unfold raw32451step2 raw32451step1; decide +kernel
      have hl : raw32451step1Labels = labelEmbedding1 ∘ raw32451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32451step1 raw32451step1Labels raw32451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw32452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32452 raw32452Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw32452 raw32452Labels = mixedMoment B raw32452step0 raw32452step0Labels := by
      have ha : raw32452step0 = (fun i j => raw32452 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32452step0 raw32452; decide +kernel
      have hl : raw32452step0Labels = raw32452Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32452 raw32452Labels permutation163 permutation5
    mixedMoment B raw32452step0 raw32452step0Labels = mixedMoment B raw32452step1 raw32452step1Labels := by
      have ha : raw32452step1 = -raw32452step0 := by apply Matrix.ext; change ∀ i j, raw32452step1 i j = -(raw32452step0 i j); unfold raw32452step1 raw32452step0; decide +kernel
      have hl : raw32452step1Labels = raw32452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32452step1 raw32452step1Labels = mixedMoment B raw32452step2 raw32452step2Labels := by
      have ha : raw32452step2 = raw32452step1 := by apply Matrix.ext; unfold raw32452step2 raw32452step1; decide +kernel
      have hl : raw32452step1Labels = labelEmbedding1 ∘ raw32452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32452step1 raw32452step1Labels raw32452step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw32453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32453step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32453step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32453 raw32453Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32453 raw32453Labels = mixedMoment B raw32453step0 raw32453step0Labels := by
      have ha : raw32453step0 = (fun i j => raw32453 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32453step0 raw32453; decide +kernel
      have hl : raw32453step0Labels = raw32453Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32453 raw32453Labels permutation163 permutation5
    mixedMoment B raw32453step0 raw32453step0Labels = mixedMoment B raw32453step1 raw32453step1Labels := by
      have ha : raw32453step1 = -raw32453step0 := by apply Matrix.ext; change ∀ i j, raw32453step1 i j = -(raw32453step0 i j); unfold raw32453step1 raw32453step0; decide +kernel
      have hl : raw32453step1Labels = raw32453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32453step1 raw32453step1Labels = mixedMoment B raw32453step2 raw32453step2Labels := by
      have ha : raw32453step2 = raw32453step1 := by apply Matrix.ext; unfold raw32453step2 raw32453step1; decide +kernel
      have hl : raw32453step1Labels = labelEmbedding1 ∘ raw32453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32453step1 raw32453step1Labels raw32453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw32454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32454step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32454 raw32454Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32454 raw32454Labels = mixedMoment B raw32454step0 raw32454step0Labels := by
      have ha : raw32454step0 = (fun i j => raw32454 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32454step0 raw32454; decide +kernel
      have hl : raw32454step0Labels = raw32454Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32454 raw32454Labels permutation205 permutation5
    mixedMoment B raw32454step0 raw32454step0Labels = mixedMoment B raw32454step1 raw32454step1Labels := by
      have ha : raw32454step1 = -raw32454step0 := by apply Matrix.ext; change ∀ i j, raw32454step1 i j = -(raw32454step0 i j); unfold raw32454step1 raw32454step0; decide +kernel
      have hl : raw32454step1Labels = raw32454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32454step1 raw32454step1Labels = mixedMoment B raw32454step2 raw32454step2Labels := by
      have ha : raw32454step2 = raw32454step1 := by apply Matrix.ext; unfold raw32454step2 raw32454step1; decide +kernel
      have hl : raw32454step1Labels = labelEmbedding1 ∘ raw32454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32454step1 raw32454step1Labels raw32454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw32455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw32455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw32455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw32455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32455 raw32455Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw32455 raw32455Labels = mixedMoment B raw32455step0 raw32455step0Labels := by
      have hz : ∀ j, raw32455 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32455step0 = (fun i j => raw32455 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32455step0 raw32455; decide +kernel
      have hl : raw32455step0Labels = raw32455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32455 raw32455Labels permutation520 hz
    mixedMoment B raw32455step0 raw32455step0Labels = mixedMoment B raw32455step1 raw32455step1Labels := by
      have ha : raw32455step1 = (fun i j => raw32455step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32455step1 raw32455step0; decide +kernel
      have hl : raw32455step1Labels = raw32455step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32455step0 raw32455step0Labels permutation35 permutation5
    mixedMoment B raw32455step1 raw32455step1Labels = mixedMoment B raw32455step2 raw32455step2Labels := by
      have ha : raw32455step2 = -raw32455step1 := by apply Matrix.ext; change ∀ i j, raw32455step2 i j = -(raw32455step1 i j); unfold raw32455step2 raw32455step1; decide +kernel
      have hl : raw32455step2Labels = raw32455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32455step2 raw32455step2Labels = mixedMoment B raw32455step3 raw32455step3Labels := by
      have ha : raw32455step3 = raw32455step2 := by apply Matrix.ext; unfold raw32455step3 raw32455step2; decide +kernel
      have hl : raw32455step2Labels = labelEmbedding1 ∘ raw32455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32455step2 raw32455step2Labels raw32455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw32456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32456 raw32456Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32456 raw32456Labels = mixedMoment B raw32456step0 raw32456step0Labels := by
      have ha : raw32456step0 = (fun i j => raw32456 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32456step0 raw32456; decide +kernel
      have hl : raw32456step0Labels = raw32456Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32456 raw32456Labels permutation249 permutation5
    mixedMoment B raw32456step0 raw32456step0Labels = mixedMoment B raw32456step1 raw32456step1Labels := by
      have ha : raw32456step1 = -raw32456step0 := by apply Matrix.ext; change ∀ i j, raw32456step1 i j = -(raw32456step0 i j); unfold raw32456step1 raw32456step0; decide +kernel
      have hl : raw32456step1Labels = raw32456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32456step1 raw32456step1Labels = mixedMoment B raw32456step2 raw32456step2Labels := by
      have ha : raw32456step2 = raw32456step1 := by apply Matrix.ext; unfold raw32456step2 raw32456step1; decide +kernel
      have hl : raw32456step1Labels = labelEmbedding1 ∘ raw32456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32456step1 raw32456step1Labels raw32456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw32457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32457 raw32457Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw32457 raw32457Labels = mixedMoment B raw32457step0 raw32457step0Labels := by
      have ha : raw32457step0 = (fun i j => raw32457 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32457step0 raw32457; decide +kernel
      have hl : raw32457step0Labels = raw32457Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32457 raw32457Labels permutation171 permutation5
    mixedMoment B raw32457step0 raw32457step0Labels = mixedMoment B raw32457step1 raw32457step1Labels := by
      have ha : raw32457step1 = -raw32457step0 := by apply Matrix.ext; change ∀ i j, raw32457step1 i j = -(raw32457step0 i j); unfold raw32457step1 raw32457step0; decide +kernel
      have hl : raw32457step1Labels = raw32457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32457step1 raw32457step1Labels = mixedMoment B raw32457step2 raw32457step2Labels := by
      have ha : raw32457step2 = raw32457step1 := by apply Matrix.ext; unfold raw32457step2 raw32457step1; decide +kernel
      have hl : raw32457step1Labels = labelEmbedding1 ∘ raw32457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32457step1 raw32457step1Labels raw32457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw32458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32458 raw32458Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw32458 raw32458Labels = mixedMoment B raw32458step0 raw32458step0Labels := by
      have ha : raw32458step0 = (fun i j => raw32458 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32458step0 raw32458; decide +kernel
      have hl : raw32458step0Labels = raw32458Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32458 raw32458Labels permutation171 permutation5
    mixedMoment B raw32458step0 raw32458step0Labels = mixedMoment B raw32458step1 raw32458step1Labels := by
      have ha : raw32458step1 = -raw32458step0 := by apply Matrix.ext; change ∀ i j, raw32458step1 i j = -(raw32458step0 i j); unfold raw32458step1 raw32458step0; decide +kernel
      have hl : raw32458step1Labels = raw32458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32458step1 raw32458step1Labels = mixedMoment B raw32458step2 raw32458step2Labels := by
      have ha : raw32458step2 = raw32458step1 := by apply Matrix.ext; unfold raw32458step2 raw32458step1; decide +kernel
      have hl : raw32458step1Labels = labelEmbedding1 ∘ raw32458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32458step1 raw32458step1Labels raw32458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw32459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw32459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32459 raw32459Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw32459 raw32459Labels = mixedMoment B raw32459step0 raw32459step0Labels := by
      have ha : raw32459step0 = (fun i j => raw32459 (permutation157 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32459step0 raw32459; decide +kernel
      have hl : raw32459step0Labels = raw32459Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32459 raw32459Labels permutation157 permutation5
    mixedMoment B raw32459step0 raw32459step0Labels = mixedMoment B raw32459step1 raw32459step1Labels := by
      have ha : raw32459step1 = -raw32459step0 := by apply Matrix.ext; change ∀ i j, raw32459step1 i j = -(raw32459step0 i j); unfold raw32459step1 raw32459step0; decide +kernel
      have hl : raw32459step1Labels = raw32459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32459step1 raw32459step1Labels = mixedMoment B raw32459step2 raw32459step2Labels := by
      have ha : raw32459step2 = raw32459step1 := by apply Matrix.ext; unfold raw32459step2 raw32459step1; decide +kernel
      have hl : raw32459step1Labels = labelEmbedding1 ∘ raw32459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32459step1 raw32459step1Labels raw32459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

def raw32460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw32460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32460 raw32460Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw32460 raw32460Labels = mixedMoment B raw32460step0 raw32460step0Labels := by
      have hz : ∀ j, raw32460 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32460step0 = (fun i j => raw32460 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32460step0 raw32460; decide +kernel
      have hl : raw32460step0Labels = raw32460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32460 raw32460Labels permutation520 hz
    mixedMoment B raw32460step0 raw32460step0Labels = mixedMoment B raw32460step1 raw32460step1Labels := by
      have ha : raw32460step1 = (fun i j => raw32460step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32460step1 raw32460step0; decide +kernel
      have hl : raw32460step1Labels = raw32460step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32460step0 raw32460step0Labels permutation36 permutation5
    mixedMoment B raw32460step1 raw32460step1Labels = mixedMoment B raw32460step2 raw32460step2Labels := by
      have ha : raw32460step2 = -raw32460step1 := by apply Matrix.ext; change ∀ i j, raw32460step2 i j = -(raw32460step1 i j); unfold raw32460step2 raw32460step1; decide +kernel
      have hl : raw32460step2Labels = raw32460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32460step2 raw32460step2Labels = mixedMoment B raw32460step3 raw32460step3Labels := by
      have ha : raw32460step3 = raw32460step2 := by apply Matrix.ext; unfold raw32460step3 raw32460step2; decide +kernel
      have hl : raw32460step2Labels = labelEmbedding1 ∘ raw32460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32460step2 raw32460step2Labels raw32460step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw32461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32461step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32461 raw32461Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32461 raw32461Labels = mixedMoment B raw32461step0 raw32461step0Labels := by
      have ha : raw32461step0 = (fun i j => raw32461 (permutation247 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32461step0 raw32461; decide +kernel
      have hl : raw32461step0Labels = raw32461Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32461 raw32461Labels permutation247 permutation5
    mixedMoment B raw32461step0 raw32461step0Labels = mixedMoment B raw32461step1 raw32461step1Labels := by
      have ha : raw32461step1 = -raw32461step0 := by apply Matrix.ext; change ∀ i j, raw32461step1 i j = -(raw32461step0 i j); unfold raw32461step1 raw32461step0; decide +kernel
      have hl : raw32461step1Labels = raw32461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32461step1 raw32461step1Labels = mixedMoment B raw32461step2 raw32461step2Labels := by
      have ha : raw32461step2 = raw32461step1 := by apply Matrix.ext; unfold raw32461step2 raw32461step1; decide +kernel
      have hl : raw32461step1Labels = labelEmbedding1 ∘ raw32461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32461step1 raw32461step1Labels raw32461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw32462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32462step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32462 raw32462Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw32462 raw32462Labels = mixedMoment B raw32462step0 raw32462step0Labels := by
      have ha : raw32462step0 = (fun i j => raw32462 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32462step0 raw32462; decide +kernel
      have hl : raw32462step0Labels = raw32462Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32462 raw32462Labels permutation162 permutation5
    mixedMoment B raw32462step0 raw32462step0Labels = mixedMoment B raw32462step1 raw32462step1Labels := by
      have ha : raw32462step1 = -raw32462step0 := by apply Matrix.ext; change ∀ i j, raw32462step1 i j = -(raw32462step0 i j); unfold raw32462step1 raw32462step0; decide +kernel
      have hl : raw32462step1Labels = raw32462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32462step1 raw32462step1Labels = mixedMoment B raw32462step2 raw32462step2Labels := by
      have ha : raw32462step2 = raw32462step1 := by apply Matrix.ext; unfold raw32462step2 raw32462step1; decide +kernel
      have hl : raw32462step1Labels = labelEmbedding1 ∘ raw32462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32462step1 raw32462step1Labels raw32462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw32463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32463 raw32463Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw32463 raw32463Labels = mixedMoment B raw32463step0 raw32463step0Labels := by
      have ha : raw32463step0 = (fun i j => raw32463 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32463step0 raw32463; decide +kernel
      have hl : raw32463step0Labels = raw32463Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32463 raw32463Labels permutation162 permutation5
    mixedMoment B raw32463step0 raw32463step0Labels = mixedMoment B raw32463step1 raw32463step1Labels := by
      have ha : raw32463step1 = -raw32463step0 := by apply Matrix.ext; change ∀ i j, raw32463step1 i j = -(raw32463step0 i j); unfold raw32463step1 raw32463step0; decide +kernel
      have hl : raw32463step1Labels = raw32463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32463step1 raw32463step1Labels = mixedMoment B raw32463step2 raw32463step2Labels := by
      have ha : raw32463step2 = raw32463step1 := by apply Matrix.ext; unfold raw32463step2 raw32463step1; decide +kernel
      have hl : raw32463step1Labels = labelEmbedding1 ∘ raw32463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32463step1 raw32463step1Labels raw32463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw32464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw32464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32464 raw32464Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw32464 raw32464Labels = mixedMoment B raw32464step0 raw32464step0Labels := by
      have ha : raw32464step0 = (fun i j => raw32464 (permutation153 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32464step0 raw32464; decide +kernel
      have hl : raw32464step0Labels = raw32464Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32464 raw32464Labels permutation153 permutation5
    mixedMoment B raw32464step0 raw32464step0Labels = mixedMoment B raw32464step1 raw32464step1Labels := by
      have ha : raw32464step1 = -raw32464step0 := by apply Matrix.ext; change ∀ i j, raw32464step1 i j = -(raw32464step0 i j); unfold raw32464step1 raw32464step0; decide +kernel
      have hl : raw32464step1Labels = raw32464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32464step1 raw32464step1Labels = mixedMoment B raw32464step2 raw32464step2Labels := by
      have ha : raw32464step2 = raw32464step1 := by apply Matrix.ext; unfold raw32464step2 raw32464step1; decide +kernel
      have hl : raw32464step1Labels = labelEmbedding1 ∘ raw32464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32464step1 raw32464step1Labels raw32464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

def raw32465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32465 raw32465Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw32465 raw32465Labels = mixedMoment B raw32465step0 raw32465step0Labels := by
      have ha : raw32465step0 = (fun i j => raw32465 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32465step0 raw32465; decide +kernel
      have hl : raw32465step0Labels = raw32465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32465 raw32465Labels permutation204 permutation5
    mixedMoment B raw32465step0 raw32465step0Labels = mixedMoment B raw32465step1 raw32465step1Labels := by
      have ha : raw32465step1 = -raw32465step0 := by apply Matrix.ext; change ∀ i j, raw32465step1 i j = -(raw32465step0 i j); unfold raw32465step1 raw32465step0; decide +kernel
      have hl : raw32465step1Labels = raw32465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32465step1 raw32465step1Labels = mixedMoment B raw32465step2 raw32465step2Labels := by
      have ha : raw32465step2 = raw32465step1 := by apply Matrix.ext; unfold raw32465step2 raw32465step1; decide +kernel
      have hl : raw32465step1Labels = labelEmbedding1 ∘ raw32465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32465step1 raw32465step1Labels raw32465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw32466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32466 raw32466Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32466 raw32466Labels = mixedMoment B raw32466step0 raw32466step0Labels := by
      have ha : raw32466step0 = (fun i j => raw32466 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32466step0 raw32466; decide +kernel
      have hl : raw32466step0Labels = raw32466Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32466 raw32466Labels permutation248 permutation5
    mixedMoment B raw32466step0 raw32466step0Labels = mixedMoment B raw32466step1 raw32466step1Labels := by
      have ha : raw32466step1 = -raw32466step0 := by apply Matrix.ext; change ∀ i j, raw32466step1 i j = -(raw32466step0 i j); unfold raw32466step1 raw32466step0; decide +kernel
      have hl : raw32466step1Labels = raw32466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32466step1 raw32466step1Labels = mixedMoment B raw32466step2 raw32466step2Labels := by
      have ha : raw32466step2 = raw32466step1 := by apply Matrix.ext; unfold raw32466step2 raw32466step1; decide +kernel
      have hl : raw32466step1Labels = labelEmbedding1 ∘ raw32466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32466step1 raw32466step1Labels raw32466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw32467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32467step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32467step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32467 raw32467Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw32467 raw32467Labels = mixedMoment B raw32467step0 raw32467step0Labels := by
      have ha : raw32467step0 = (fun i j => raw32467 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32467step0 raw32467; decide +kernel
      have hl : raw32467step0Labels = raw32467Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32467 raw32467Labels permutation158 permutation5
    mixedMoment B raw32467step0 raw32467step0Labels = mixedMoment B raw32467step1 raw32467step1Labels := by
      have ha : raw32467step1 = -raw32467step0 := by apply Matrix.ext; change ∀ i j, raw32467step1 i j = -(raw32467step0 i j); unfold raw32467step1 raw32467step0; decide +kernel
      have hl : raw32467step1Labels = raw32467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32467step1 raw32467step1Labels = mixedMoment B raw32467step2 raw32467step2Labels := by
      have ha : raw32467step2 = raw32467step1 := by apply Matrix.ext; unfold raw32467step2 raw32467step1; decide +kernel
      have hl : raw32467step1Labels = labelEmbedding1 ∘ raw32467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32467step1 raw32467step1Labels raw32467step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw32468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32468 raw32468Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw32468 raw32468Labels = mixedMoment B raw32468step0 raw32468step0Labels := by
      have ha : raw32468step0 = (fun i j => raw32468 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32468step0 raw32468; decide +kernel
      have hl : raw32468step0Labels = raw32468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32468 raw32468Labels permutation158 permutation5
    mixedMoment B raw32468step0 raw32468step0Labels = mixedMoment B raw32468step1 raw32468step1Labels := by
      have ha : raw32468step1 = -raw32468step0 := by apply Matrix.ext; change ∀ i j, raw32468step1 i j = -(raw32468step0 i j); unfold raw32468step1 raw32468step0; decide +kernel
      have hl : raw32468step1Labels = raw32468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32468step1 raw32468step1Labels = mixedMoment B raw32468step2 raw32468step2Labels := by
      have ha : raw32468step2 = raw32468step1 := by apply Matrix.ext; unfold raw32468step2 raw32468step1; decide +kernel
      have hl : raw32468step1Labels = labelEmbedding1 ∘ raw32468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32468step1 raw32468step1Labels raw32468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw32469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32469 raw32469Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw32469 raw32469Labels = mixedMoment B raw32469step0 raw32469step0Labels := by
      have ha : raw32469step0 = (fun i j => raw32469 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32469step0 raw32469; decide +kernel
      have hl : raw32469step0Labels = raw32469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32469 raw32469Labels permutation662 permutation7
    mixedMoment B raw32469step0 raw32469step0Labels = mixedMoment B raw32469step1 raw32469step1Labels := by
      have ha : raw32469step1 = raw32469step0 := by apply Matrix.ext; unfold raw32469step1 raw32469step0; decide +kernel
      have hl : raw32469step0Labels = labelEmbedding1 ∘ raw32469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32469step0 raw32469step0Labels raw32469step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw32470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw32470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32470step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32470 raw32470Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32470 raw32470Labels = mixedMoment B raw32470step0 raw32470step0Labels := by
      have ha : raw32470step0 = (fun i j => raw32470 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32470step0 raw32470; decide +kernel
      have hl : raw32470step0Labels = raw32470Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32470 raw32470Labels permutation200 permutation5
    mixedMoment B raw32470step0 raw32470step0Labels = mixedMoment B raw32470step1 raw32470step1Labels := by
      have ha : raw32470step1 = -raw32470step0 := by apply Matrix.ext; change ∀ i j, raw32470step1 i j = -(raw32470step0 i j); unfold raw32470step1 raw32470step0; decide +kernel
      have hl : raw32470step1Labels = raw32470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32470step1 raw32470step1Labels = mixedMoment B raw32470step2 raw32470step2Labels := by
      have ha : raw32470step2 = raw32470step1 := by apply Matrix.ext; unfold raw32470step2 raw32470step1; decide +kernel
      have hl : raw32470step1Labels = labelEmbedding1 ∘ raw32470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32470step1 raw32470step1Labels raw32470step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw32471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32471 raw32471Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw32471 raw32471Labels = mixedMoment B raw32471step0 raw32471step0Labels := by
      have hz : ∀ j, raw32471 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32471step0 = (fun i j => raw32471 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32471step0 raw32471; decide +kernel
      have hl : raw32471step0Labels = raw32471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32471 raw32471Labels permutation520 hz
    mixedMoment B raw32471step0 raw32471step0Labels = mixedMoment B raw32471step1 raw32471step1Labels := by
      have ha : raw32471step1 = (fun i j => raw32471step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32471step1 raw32471step0; decide +kernel
      have hl : raw32471step1Labels = raw32471step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32471step0 raw32471step0Labels permutation151 permutation7
    mixedMoment B raw32471step1 raw32471step1Labels = mixedMoment B raw32471step2 raw32471step2Labels := by
      have ha : raw32471step2 = raw32471step1 := by apply Matrix.ext; unfold raw32471step2 raw32471step1; decide +kernel
      have hl : raw32471step1Labels = labelEmbedding1 ∘ raw32471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32471step1 raw32471step1Labels raw32471step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw32472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32472 raw32472Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw32472 raw32472Labels = mixedMoment B raw32472step0 raw32472step0Labels := by
      have ha : raw32472step0 = (fun i j => raw32472 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32472step0 raw32472; decide +kernel
      have hl : raw32472step0Labels = raw32472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32472 raw32472Labels permutation663 permutation2
    mixedMoment B raw32472step0 raw32472step0Labels = mixedMoment B raw32472step1 raw32472step1Labels := by
      have ha : raw32472step1 = -raw32472step0 := by apply Matrix.ext; change ∀ i j, raw32472step1 i j = -(raw32472step0 i j); unfold raw32472step1 raw32472step0; decide +kernel
      have hl : raw32472step1Labels = raw32472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw32473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32473 raw32473Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw32473 raw32473Labels = mixedMoment B raw32473step0 raw32473step0Labels := by
      have ha : raw32473step0 = (fun i j => raw32473 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32473step0 raw32473; decide +kernel
      have hl : raw32473step0Labels = raw32473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32473 raw32473Labels permutation154 permutation2
    _ = mixedMoment B node2826 node2826Labels := by rfl

def raw32474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32474 raw32474Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw32474 raw32474Labels = mixedMoment B raw32474step0 raw32474step0Labels := by
      have ha : raw32474step0 = (fun i j => raw32474 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32474step0 raw32474; decide +kernel
      have hl : raw32474step0Labels = raw32474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32474 raw32474Labels permutation154 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

def raw32475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32475 raw32475Labels = mixedMoment B node2824 node2824Labels := by
  calc
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw32476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw32476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw32476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32476 raw32476Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw32476 raw32476Labels = mixedMoment B raw32476step0 raw32476step0Labels := by
      have ha : raw32476step0 = (fun i j => raw32476 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32476step0 raw32476; decide +kernel
      have hl : raw32476step0Labels = raw32476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32476 raw32476Labels permutation664 permutation2
    mixedMoment B raw32476step0 raw32476step0Labels = mixedMoment B raw32476step1 raw32476step1Labels := by
      have ha : raw32476step1 = -raw32476step0 := by apply Matrix.ext; change ∀ i j, raw32476step1 i j = -(raw32476step0 i j); unfold raw32476step1 raw32476step0; decide +kernel
      have hl : raw32476step1Labels = raw32476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2422 node2422Labels := by rfl

def raw32477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32477step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32477 raw32477Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32477 raw32477Labels = mixedMoment B raw32477step0 raw32477step0Labels := by
      have ha : raw32477step0 = (fun i j => raw32477 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32477step0 raw32477; decide +kernel
      have hl : raw32477step0Labels = raw32477Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32477 raw32477Labels permutation154 permutation7
    mixedMoment B raw32477step0 raw32477step0Labels = mixedMoment B raw32477step1 raw32477step1Labels := by
      have ha : raw32477step1 = raw32477step0 := by apply Matrix.ext; unfold raw32477step1 raw32477step0; decide +kernel
      have hl : raw32477step0Labels = labelEmbedding10 ∘ raw32477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32477step0 raw32477step0Labels raw32477step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw32478step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw32478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32478 raw32478Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw32478 raw32478Labels = mixedMoment B raw32478step0 raw32478step0Labels := by
      have ha : raw32478step0 = (fun i j => raw32478 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32478step0 raw32478; decide +kernel
      have hl : raw32478step0Labels = raw32478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32478 raw32478Labels permutation154 permutation7
    mixedMoment B raw32478step0 raw32478step0Labels = mixedMoment B raw32478step1 raw32478step1Labels := by
      have ha : raw32478step1 = raw32478step0 := by apply Matrix.ext; unfold raw32478step1 raw32478step0; decide +kernel
      have hl : raw32478step0Labels = labelEmbedding10 ∘ raw32478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32478step0 raw32478step0Labels raw32478step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw32479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw32479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32479 raw32479Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw32479 raw32479Labels = mixedMoment B raw32479step0 raw32479step0Labels := by
      have ha : raw32479step0 = (fun i j => raw32479 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32479step0 raw32479; decide +kernel
      have hl : raw32479step0Labels = raw32479Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32479 raw32479Labels permutation664 permutation2
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw32480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32480step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32480 raw32480Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw32480 raw32480Labels = mixedMoment B raw32480step0 raw32480step0Labels := by
      have ha : raw32480step0 = (fun i j => raw32480 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32480step0 raw32480; decide +kernel
      have hl : raw32480step0Labels = raw32480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32480 raw32480Labels permutation152 permutation6
    mixedMoment B raw32480step0 raw32480step0Labels = mixedMoment B raw32480step1 raw32480step1Labels := by
      have ha : raw32480step1 = raw32480step0 := by apply Matrix.ext; unfold raw32480step1 raw32480step0; decide +kernel
      have hl : raw32480step0Labels = labelEmbedding9 ∘ raw32480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32480step0 raw32480step0Labels raw32480step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw32481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32481step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32481 raw32481Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw32481 raw32481Labels = mixedMoment B raw32481step0 raw32481step0Labels := by
      have ha : raw32481step0 = (fun i j => raw32481 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32481step0 raw32481; decide +kernel
      have hl : raw32481step0Labels = raw32481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32481 raw32481Labels permutation152 permutation6
    mixedMoment B raw32481step0 raw32481step0Labels = mixedMoment B raw32481step1 raw32481step1Labels := by
      have ha : raw32481step1 = raw32481step0 := by apply Matrix.ext; unfold raw32481step1 raw32481step0; decide +kernel
      have hl : raw32481step0Labels = labelEmbedding9 ∘ raw32481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32481step0 raw32481step0Labels raw32481step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw32482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw32482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32482 raw32482Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw32482 raw32482Labels = mixedMoment B raw32482step0 raw32482step0Labels := by
      have ha : raw32482step0 = (fun i j => raw32482 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32482step0 raw32482; decide +kernel
      have hl : raw32482step0Labels = raw32482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32482 raw32482Labels permutation663 permutation2
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw32483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32483step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32483 raw32483Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw32483 raw32483Labels = mixedMoment B raw32483step0 raw32483step0Labels := by
      have ha : raw32483step0 = (fun i j => raw32483 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32483step0 raw32483; decide +kernel
      have hl : raw32483step0Labels = raw32483Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32483 raw32483Labels permutation152 permutation6
    mixedMoment B raw32483step0 raw32483step0Labels = mixedMoment B raw32483step1 raw32483step1Labels := by
      have ha : raw32483step1 = raw32483step0 := by apply Matrix.ext; unfold raw32483step1 raw32483step0; decide +kernel
      have hl : raw32483step0Labels = labelEmbedding9 ∘ raw32483step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32483step0 raw32483step0Labels raw32483step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw32484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32484step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32484 raw32484Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw32484 raw32484Labels = mixedMoment B raw32484step0 raw32484step0Labels := by
      have ha : raw32484step0 = (fun i j => raw32484 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32484step0 raw32484; decide +kernel
      have hl : raw32484step0Labels = raw32484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32484 raw32484Labels permutation152 permutation6
    mixedMoment B raw32484step0 raw32484step0Labels = mixedMoment B raw32484step1 raw32484step1Labels := by
      have ha : raw32484step1 = raw32484step0 := by apply Matrix.ext; unfold raw32484step1 raw32484step0; decide +kernel
      have hl : raw32484step0Labels = labelEmbedding9 ∘ raw32484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32484step0 raw32484step0Labels raw32484step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw32485 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32485step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw32485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32485 raw32485Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw32485 raw32485Labels = mixedMoment B raw32485step0 raw32485step0Labels := by
      have ha : raw32485step0 = (fun i j => raw32485 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32485step0 raw32485; decide +kernel
      have hl : raw32485step0Labels = raw32485Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32485 raw32485Labels permutation152 permutation6
    mixedMoment B raw32485step0 raw32485step0Labels = mixedMoment B raw32485step1 raw32485step1Labels := by
      have ha : raw32485step1 = raw32485step0 := by apply Matrix.ext; unfold raw32485step1 raw32485step0; decide +kernel
      have hl : raw32485step0Labels = labelEmbedding9 ∘ raw32485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32485step0 raw32485step0Labels raw32485step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw32486 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw32486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32486 raw32486Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw32486 raw32486Labels = mixedMoment B raw32486step0 raw32486step0Labels := by
      have ha : raw32486step0 = (fun i j => raw32486 (permutation661 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32486step0 raw32486; decide +kernel
      have hl : raw32486step0Labels = raw32486Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32486 raw32486Labels permutation661 permutation2
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw32487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32487 raw32487Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32487 raw32487Labels = mixedMoment B raw32487step0 raw32487step0Labels := by
      have hz : ∀ j, raw32487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32487step0 = (fun i j => raw32487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32487step0 raw32487; decide +kernel
      have hl : raw32487step0Labels = raw32487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32487 raw32487Labels permutation346 hz
    mixedMoment B raw32487step0 raw32487step0Labels = mixedMoment B raw32487step1 raw32487step1Labels := by
      have ha : raw32487step1 = (fun i j => raw32487step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32487step1 raw32487step0; decide +kernel
      have hl : raw32487step1Labels = raw32487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32487step0 raw32487step0Labels permutation32 permutation6
    mixedMoment B raw32487step1 raw32487step1Labels = mixedMoment B raw32487step2 raw32487step2Labels := by
      have ha : raw32487step2 = raw32487step1 := by apply Matrix.ext; unfold raw32487step2 raw32487step1; decide +kernel
      have hl : raw32487step1Labels = labelEmbedding9 ∘ raw32487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32487step1 raw32487step1Labels raw32487step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw32488 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32488step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32488 raw32488Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw32488 raw32488Labels = mixedMoment B raw32488step0 raw32488step0Labels := by
      have ha : raw32488step0 = (fun i j => raw32488 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32488step0 raw32488; decide +kernel
      have hl : raw32488step0Labels = raw32488Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32488 raw32488Labels permutation152 permutation6
    mixedMoment B raw32488step0 raw32488step0Labels = mixedMoment B raw32488step1 raw32488step1Labels := by
      have ha : raw32488step1 = raw32488step0 := by apply Matrix.ext; unfold raw32488step1 raw32488step0; decide +kernel
      have hl : raw32488step0Labels = labelEmbedding9 ∘ raw32488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32488step0 raw32488step0Labels raw32488step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw32489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32489step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32489 raw32489Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw32489 raw32489Labels = mixedMoment B raw32489step0 raw32489step0Labels := by
      have ha : raw32489step0 = (fun i j => raw32489 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32489step0 raw32489; decide +kernel
      have hl : raw32489step0Labels = raw32489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32489 raw32489Labels permutation152 permutation6
    mixedMoment B raw32489step0 raw32489step0Labels = mixedMoment B raw32489step1 raw32489step1Labels := by
      have ha : raw32489step1 = raw32489step0 := by apply Matrix.ext; unfold raw32489step1 raw32489step0; decide +kernel
      have hl : raw32489step0Labels = labelEmbedding9 ∘ raw32489step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32489step0 raw32489step0Labels raw32489step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw32490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw32490step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw32490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32490 raw32490Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw32490 raw32490Labels = mixedMoment B raw32490step0 raw32490step0Labels := by
      have ha : raw32490step0 = (fun i j => raw32490 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32490step0 raw32490; decide +kernel
      have hl : raw32490step0Labels = raw32490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32490 raw32490Labels permutation152 permutation6
    mixedMoment B raw32490step0 raw32490step0Labels = mixedMoment B raw32490step1 raw32490step1Labels := by
      have ha : raw32490step1 = raw32490step0 := by apply Matrix.ext; unfold raw32490step1 raw32490step0; decide +kernel
      have hl : raw32490step0Labels = labelEmbedding9 ∘ raw32490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32490step0 raw32490step0Labels raw32490step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5146 node5146Labels := by rfl

def raw32491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw32491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32491 raw32491Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw32491 raw32491Labels = mixedMoment B raw32491step0 raw32491step0Labels := by
      have ha : raw32491step0 = (fun i j => raw32491 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32491step0 raw32491; decide +kernel
      have hl : raw32491step0Labels = raw32491Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32491 raw32491Labels permutation664 permutation2
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw32492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32492step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32492 raw32492Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw32492 raw32492Labels = mixedMoment B raw32492step0 raw32492step0Labels := by
      have ha : raw32492step0 = (fun i j => raw32492 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32492step0 raw32492; decide +kernel
      have hl : raw32492step0Labels = raw32492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32492 raw32492Labels permutation152 permutation6
    mixedMoment B raw32492step0 raw32492step0Labels = mixedMoment B raw32492step1 raw32492step1Labels := by
      have ha : raw32492step1 = raw32492step0 := by apply Matrix.ext; unfold raw32492step1 raw32492step0; decide +kernel
      have hl : raw32492step0Labels = labelEmbedding9 ∘ raw32492step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32492step0 raw32492step0Labels raw32492step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw32493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32493 raw32493Labels = mixedMoment B node1169 node1169Labels := by
  calc
    _ = mixedMoment B node1169 node1169Labels := by rfl

def raw32494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32494 raw32494Labels = mixedMoment B node2361 node2361Labels := by
  calc
    _ = mixedMoment B node2361 node2361Labels := by rfl

def raw32495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw32495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32495 raw32495Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw32495 raw32495Labels = mixedMoment B raw32495step0 raw32495step0Labels := by
      have ha : raw32495step0 = (fun i j => raw32495 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32495step0 raw32495; decide +kernel
      have hl : raw32495step0Labels = raw32495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32495 raw32495Labels permutation164 permutation2
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw32496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw32496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32496 raw32496Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw32496 raw32496Labels = mixedMoment B raw32496step0 raw32496step0Labels := by
      have ha : raw32496step0 = (fun i j => raw32496 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32496step0 raw32496; decide +kernel
      have hl : raw32496step0Labels = raw32496Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32496 raw32496Labels permutation170 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw32497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32497 raw32497Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw32497 raw32497Labels = mixedMoment B raw32497step0 raw32497step0Labels := by
      have ha : raw32497step0 = (fun i j => raw32497 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32497step0 raw32497; decide +kernel
      have hl : raw32497step0Labels = raw32497Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32497 raw32497Labels permutation662 permutation2
    mixedMoment B raw32497step0 raw32497step0Labels = mixedMoment B raw32497step1 raw32497step1Labels := by
      have ha : raw32497step1 = -raw32497step0 := by apply Matrix.ext; change ∀ i j, raw32497step1 i j = -(raw32497step0 i j); unfold raw32497step1 raw32497step0; decide +kernel
      have hl : raw32497step1Labels = raw32497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw32498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32498 raw32498Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw32498 raw32498Labels = mixedMoment B raw32498step0 raw32498step0Labels := by
      have ha : raw32498step0 = (fun i j => raw32498 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32498step0 raw32498; decide +kernel
      have hl : raw32498step0Labels = raw32498Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32498 raw32498Labels permutation176 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw32499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32499 raw32499Labels = mixedMoment B node2923 node2923Labels := by
  calc
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw32500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32500 raw32500Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw32500 raw32500Labels = mixedMoment B raw32500step0 raw32500step0Labels := by
      have ha : raw32500step0 = (fun i j => raw32500 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32500step0 raw32500; decide +kernel
      have hl : raw32500step0Labels = raw32500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32500 raw32500Labels permutation154 permutation2
    _ = mixedMoment B node2892 node2892Labels := by rfl

def raw32501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32501 raw32501Labels = mixedMoment B node2892 node2892Labels := by
  calc
    _ = mixedMoment B node2892 node2892Labels := by rfl

def raw32502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw32502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32502 raw32502Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw32502 raw32502Labels = mixedMoment B raw32502step0 raw32502step0Labels := by
      have ha : raw32502step0 = (fun i j => raw32502 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32502step0 raw32502; decide +kernel
      have hl : raw32502step0Labels = raw32502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32502 raw32502Labels permutation662 permutation2
    mixedMoment B raw32502step0 raw32502step0Labels = mixedMoment B raw32502step1 raw32502step1Labels := by
      have ha : raw32502step1 = -raw32502step0 := by apply Matrix.ext; change ∀ i j, raw32502step1 i j = -(raw32502step0 i j); unfold raw32502step1 raw32502step0; decide +kernel
      have hl : raw32502step1Labels = raw32502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw32503 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw32503Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw32503step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw32503step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw32503step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32503step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw32503step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32503 raw32503Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw32503 raw32503Labels = mixedMoment B raw32503step0 raw32503step0Labels := by
      have hz : ∀ j, raw32503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32503step0 = (fun i j => raw32503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32503step0 raw32503; decide +kernel
      have hl : raw32503step0Labels = raw32503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32503 raw32503Labels permutation520 hz
    mixedMoment B raw32503step0 raw32503step0Labels = mixedMoment B raw32503step1 raw32503step1Labels := by
      have hz : ∀ j, raw32503step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw32503step1 = (fun i j => raw32503step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw32503step1 raw32503step0; decide +kernel
      have hl : raw32503step1Labels = raw32503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32503step0 raw32503step0Labels permutation104 hz
    mixedMoment B raw32503step1 raw32503step1Labels = mixedMoment B raw32503step2 raw32503step2Labels := by
      have ha : raw32503step2 = (fun i j => raw32503step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32503step2 raw32503step1; decide +kernel
      have hl : raw32503step2Labels = raw32503step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32503step1 raw32503step1Labels permutation26 permutation0
    mixedMoment B raw32503step2 raw32503step2Labels = mixedMoment B raw32503step3 raw32503step3Labels := by
      have ha : raw32503step3 = -raw32503step2 := by apply Matrix.ext; change ∀ i j, raw32503step3 i j = -(raw32503step2 i j); unfold raw32503step3 raw32503step2; decide +kernel
      have hl : raw32503step3Labels = raw32503step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw32504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32504 raw32504Labels = mixedMoment B node3777 node3777Labels := by
  calc
    mixedMoment B raw32504 raw32504Labels = mixedMoment B raw32504step0 raw32504step0Labels := by
      have ha : raw32504step0 = (fun i j => raw32504 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32504step0 raw32504; decide +kernel
      have hl : raw32504step0Labels = raw32504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32504 raw32504Labels permutation662 permutation2
    mixedMoment B raw32504step0 raw32504step0Labels = mixedMoment B raw32504step1 raw32504step1Labels := by
      have ha : raw32504step1 = -raw32504step0 := by apply Matrix.ext; change ∀ i j, raw32504step1 i j = -(raw32504step0 i j); unfold raw32504step1 raw32504step0; decide +kernel
      have hl : raw32504step1Labels = raw32504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3777 node3777Labels := by rfl

def raw32505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32505 raw32505Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32505 raw32505Labels = mixedMoment B raw32505step0 raw32505step0Labels := by
      have ha : raw32505step0 = (fun i j => raw32505 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32505step0 raw32505; decide +kernel
      have hl : raw32505step0Labels = raw32505Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32505 raw32505Labels permutation178 permutation2
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32506 raw32506Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32506 raw32506Labels = mixedMoment B raw32506step0 raw32506step0Labels := by
      have ha : raw32506step0 = (fun i j => raw32506 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32506step0 raw32506; decide +kernel
      have hl : raw32506step0Labels = raw32506Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32506 raw32506Labels permutation176 permutation2
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32507 raw32507Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw32507 raw32507Labels = mixedMoment B raw32507step0 raw32507step0Labels := by
      have ha : raw32507step0 = (fun i j => raw32507 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32507step0 raw32507; decide +kernel
      have hl : raw32507step0Labels = raw32507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32507 raw32507Labels permutation662 permutation2
    mixedMoment B raw32507step0 raw32507step0Labels = mixedMoment B raw32507step1 raw32507step1Labels := by
      have ha : raw32507step1 = -raw32507step0 := by apply Matrix.ext; change ∀ i j, raw32507step1 i j = -(raw32507step0 i j); unfold raw32507step1 raw32507step0; decide +kernel
      have hl : raw32507step1Labels = raw32507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw32508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32508 raw32508Labels = mixedMoment B node3435 node3435Labels := by
  calc
    mixedMoment B raw32508 raw32508Labels = mixedMoment B raw32508step0 raw32508step0Labels := by
      have ha : raw32508step0 = -raw32508 := by apply Matrix.ext; change ∀ i j, raw32508step0 i j = -(raw32508 i j); unfold raw32508step0 raw32508; decide +kernel
      have hl : raw32508step0Labels = raw32508Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3435 node3435Labels := by rfl

def raw32509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw32509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32509 raw32509Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw32509 raw32509Labels = mixedMoment B raw32509step0 raw32509step0Labels := by
      have ha : raw32509step0 = (fun i j => raw32509 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32509step0 raw32509; decide +kernel
      have hl : raw32509step0Labels = raw32509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32509 raw32509Labels permutation178 permutation2
    mixedMoment B raw32509step0 raw32509step0Labels = mixedMoment B raw32509step1 raw32509step1Labels := by
      have ha : raw32509step1 = -raw32509step0 := by apply Matrix.ext; change ∀ i j, raw32509step1 i j = -(raw32509step0 i j); unfold raw32509step1 raw32509step0; decide +kernel
      have hl : raw32509step1Labels = raw32509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw32510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw32510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw32510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32510 raw32510Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw32510 raw32510Labels = mixedMoment B raw32510step0 raw32510step0Labels := by
      have ha : raw32510step0 = (fun i j => raw32510 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32510step0 raw32510; decide +kernel
      have hl : raw32510step0Labels = raw32510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32510 raw32510Labels permutation176 permutation2
    mixedMoment B raw32510step0 raw32510step0Labels = mixedMoment B raw32510step1 raw32510step1Labels := by
      have ha : raw32510step1 = -raw32510step0 := by apply Matrix.ext; change ∀ i j, raw32510step1 i j = -(raw32510step0 i j); unfold raw32510step1 raw32510step0; decide +kernel
      have hl : raw32510step1Labels = raw32510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw32511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw32511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw32511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32511 raw32511Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw32511 raw32511Labels = mixedMoment B raw32511step0 raw32511step0Labels := by
      have ha : raw32511step0 = (fun i j => raw32511 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32511step0 raw32511; decide +kernel
      have hl : raw32511step0Labels = raw32511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32511 raw32511Labels permutation662 permutation2
    _ = mixedMoment B node2417 node2417Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
