import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34560 raw34560Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw34560 raw34560Labels = mixedMoment B raw34560step0 raw34560step0Labels := by
      have ha : raw34560step0 = (fun i j => raw34560 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34560step0 raw34560; decide +kernel
      have hl : raw34560step0Labels = raw34560Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34560 raw34560Labels permutation168 permutation6
    mixedMoment B raw34560step0 raw34560step0Labels = mixedMoment B raw34560step1 raw34560step1Labels := by
      have ha : raw34560step1 = raw34560step0 := by apply Matrix.ext; unfold raw34560step1 raw34560step0; decide +kernel
      have hl : raw34560step0Labels = labelEmbedding9 ∘ raw34560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34560step0 raw34560step0Labels raw34560step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw34561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34561step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34561 raw34561Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw34561 raw34561Labels = mixedMoment B raw34561step0 raw34561step0Labels := by
      have ha : raw34561step0 = (fun i j => raw34561 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34561step0 raw34561; decide +kernel
      have hl : raw34561step0Labels = raw34561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34561 raw34561Labels permutation282 permutation3
    mixedMoment B raw34561step0 raw34561step0Labels = mixedMoment B raw34561step1 raw34561step1Labels := by
      have ha : raw34561step1 = raw34561step0 := by apply Matrix.ext; unfold raw34561step1 raw34561step0; decide +kernel
      have hl : raw34561step0Labels = labelEmbedding6 ∘ raw34561step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34561step0 raw34561step0Labels raw34561step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw34562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34562 raw34562Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw34562 raw34562Labels = mixedMoment B raw34562step0 raw34562step0Labels := by
      have hz : ∀ j, raw34562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34562step0 = (fun i j => raw34562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34562step0 raw34562; decide +kernel
      have hl : raw34562step0Labels = raw34562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34562 raw34562Labels permutation434 hz
    mixedMoment B raw34562step0 raw34562step0Labels = mixedMoment B raw34562step1 raw34562step1Labels := by
      have ha : raw34562step1 = (fun i j => raw34562step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34562step1 raw34562step0; decide +kernel
      have hl : raw34562step1Labels = raw34562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34562step0 raw34562step0Labels permutation35 permutation3
    mixedMoment B raw34562step1 raw34562step1Labels = mixedMoment B raw34562step2 raw34562step2Labels := by
      have ha : raw34562step2 = raw34562step1 := by apply Matrix.ext; unfold raw34562step2 raw34562step1; decide +kernel
      have hl : raw34562step1Labels = labelEmbedding6 ∘ raw34562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34562step1 raw34562step1Labels raw34562step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw34563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34563 raw34563Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw34563 raw34563Labels = mixedMoment B raw34563step0 raw34563step0Labels := by
      have ha : raw34563step0 = (fun i j => raw34563 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34563step0 raw34563; decide +kernel
      have hl : raw34563step0Labels = raw34563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34563 raw34563Labels permutation169 permutation3
    mixedMoment B raw34563step0 raw34563step0Labels = mixedMoment B raw34563step1 raw34563step1Labels := by
      have ha : raw34563step1 = raw34563step0 := by apply Matrix.ext; unfold raw34563step1 raw34563step0; decide +kernel
      have hl : raw34563step0Labels = labelEmbedding6 ∘ raw34563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34563step0 raw34563step0Labels raw34563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw34564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34564step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34564 raw34564Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw34564 raw34564Labels = mixedMoment B raw34564step0 raw34564step0Labels := by
      have ha : raw34564step0 = (fun i j => raw34564 (permutation175 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34564step0 raw34564; decide +kernel
      have hl : raw34564step0Labels = raw34564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34564 raw34564Labels permutation175 permutation3
    mixedMoment B raw34564step0 raw34564step0Labels = mixedMoment B raw34564step1 raw34564step1Labels := by
      have ha : raw34564step1 = raw34564step0 := by apply Matrix.ext; unfold raw34564step1 raw34564step0; decide +kernel
      have hl : raw34564step0Labels = labelEmbedding6 ∘ raw34564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34564step0 raw34564step0Labels raw34564step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw34565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34565 raw34565Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw34565 raw34565Labels = mixedMoment B raw34565step0 raw34565step0Labels := by
      have hz : ∀ j, raw34565 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34565step0 = (fun i j => raw34565 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34565step0 raw34565; decide +kernel
      have hl : raw34565step0Labels = raw34565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34565 raw34565Labels permutation265 hz
    mixedMoment B raw34565step0 raw34565step0Labels = mixedMoment B raw34565step1 raw34565step1Labels := by
      have ha : raw34565step1 = (fun i j => raw34565step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34565step1 raw34565step0; decide +kernel
      have hl : raw34565step1Labels = raw34565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34565step0 raw34565step0Labels permutation49 permutation3
    mixedMoment B raw34565step1 raw34565step1Labels = mixedMoment B raw34565step2 raw34565step2Labels := by
      have ha : raw34565step2 = raw34565step1 := by apply Matrix.ext; unfold raw34565step2 raw34565step1; decide +kernel
      have hl : raw34565step1Labels = labelEmbedding6 ∘ raw34565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34565step1 raw34565step1Labels raw34565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw34566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34566step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34566 raw34566Labels = mixedMoment B node4909 node4909Labels := by
  calc
    mixedMoment B raw34566 raw34566Labels = mixedMoment B raw34566step0 raw34566step0Labels := by
      have ha : raw34566step0 = (fun i j => raw34566 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34566step0 raw34566; decide +kernel
      have hl : raw34566step0Labels = raw34566Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34566 raw34566Labels permutation169 permutation3
    mixedMoment B raw34566step0 raw34566step0Labels = mixedMoment B raw34566step1 raw34566step1Labels := by
      have ha : raw34566step1 = raw34566step0 := by apply Matrix.ext; unfold raw34566step1 raw34566step0; decide +kernel
      have hl : raw34566step0Labels = labelEmbedding6 ∘ raw34566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34566step0 raw34566step0Labels raw34566step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4909 node4909Labels := by rfl

def raw34567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34567step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34567 raw34567Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw34567 raw34567Labels = mixedMoment B raw34567step0 raw34567step0Labels := by
      have hz : ∀ j, raw34567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34567step0 = (fun i j => raw34567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34567step0 raw34567; decide +kernel
      have hl : raw34567step0Labels = raw34567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34567 raw34567Labels permutation434 hz
    mixedMoment B raw34567step0 raw34567step0Labels = mixedMoment B raw34567step1 raw34567step1Labels := by
      have ha : raw34567step1 = (fun i j => raw34567step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34567step1 raw34567step0; decide +kernel
      have hl : raw34567step1Labels = raw34567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34567step0 raw34567step0Labels permutation35 permutation3
    mixedMoment B raw34567step1 raw34567step1Labels = mixedMoment B raw34567step2 raw34567step2Labels := by
      have ha : raw34567step2 = raw34567step1 := by apply Matrix.ext; unfold raw34567step2 raw34567step1; decide +kernel
      have hl : raw34567step1Labels = labelEmbedding6 ∘ raw34567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34567step1 raw34567step1Labels raw34567step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw34568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34568 raw34568Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw34568 raw34568Labels = mixedMoment B raw34568step0 raw34568step0Labels := by
      have ha : raw34568step0 = (fun i j => raw34568 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34568step0 raw34568; decide +kernel
      have hl : raw34568step0Labels = raw34568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34568 raw34568Labels permutation169 permutation3
    mixedMoment B raw34568step0 raw34568step0Labels = mixedMoment B raw34568step1 raw34568step1Labels := by
      have ha : raw34568step1 = raw34568step0 := by apply Matrix.ext; unfold raw34568step1 raw34568step0; decide +kernel
      have hl : raw34568step0Labels = labelEmbedding6 ∘ raw34568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34568step0 raw34568step0Labels raw34568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw34569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34569step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw34569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34569 raw34569Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw34569 raw34569Labels = mixedMoment B raw34569step0 raw34569step0Labels := by
      have ha : raw34569step0 = (fun i j => raw34569 (permutation175 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34569step0 raw34569; decide +kernel
      have hl : raw34569step0Labels = raw34569Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34569 raw34569Labels permutation175 permutation3
    mixedMoment B raw34569step0 raw34569step0Labels = mixedMoment B raw34569step1 raw34569step1Labels := by
      have ha : raw34569step1 = raw34569step0 := by apply Matrix.ext; unfold raw34569step1 raw34569step0; decide +kernel
      have hl : raw34569step0Labels = labelEmbedding6 ∘ raw34569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34569step0 raw34569step0Labels raw34569step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw34570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34570 raw34570Labels = mixedMoment B node4910 node4910Labels := by
  calc
    mixedMoment B raw34570 raw34570Labels = mixedMoment B raw34570step0 raw34570step0Labels := by
      have ha : raw34570step0 = (fun i j => raw34570 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34570step0 raw34570; decide +kernel
      have hl : raw34570step0Labels = raw34570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34570 raw34570Labels permutation168 permutation3
    mixedMoment B raw34570step0 raw34570step0Labels = mixedMoment B raw34570step1 raw34570step1Labels := by
      have ha : raw34570step1 = raw34570step0 := by apply Matrix.ext; unfold raw34570step1 raw34570step0; decide +kernel
      have hl : raw34570step0Labels = labelEmbedding6 ∘ raw34570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34570step0 raw34570step0Labels raw34570step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4910 node4910Labels := by rfl

def raw34571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34571 raw34571Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw34571 raw34571Labels = mixedMoment B raw34571step0 raw34571step0Labels := by
      have ha : raw34571step0 = (fun i j => raw34571 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34571step0 raw34571; decide +kernel
      have hl : raw34571step0Labels = raw34571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34571 raw34571Labels permutation168 permutation3
    mixedMoment B raw34571step0 raw34571step0Labels = mixedMoment B raw34571step1 raw34571step1Labels := by
      have ha : raw34571step1 = raw34571step0 := by apply Matrix.ext; unfold raw34571step1 raw34571step0; decide +kernel
      have hl : raw34571step0Labels = labelEmbedding6 ∘ raw34571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34571step0 raw34571step0Labels raw34571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw34572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34572 raw34572Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw34572 raw34572Labels = mixedMoment B raw34572step0 raw34572step0Labels := by
      have ha : raw34572step0 = (fun i j => raw34572 (permutation174 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34572step0 raw34572; decide +kernel
      have hl : raw34572step0Labels = raw34572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34572 raw34572Labels permutation174 permutation3
    mixedMoment B raw34572step0 raw34572step0Labels = mixedMoment B raw34572step1 raw34572step1Labels := by
      have ha : raw34572step1 = raw34572step0 := by apply Matrix.ext; unfold raw34572step1 raw34572step0; decide +kernel
      have hl : raw34572step0Labels = labelEmbedding6 ∘ raw34572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34572step0 raw34572step0Labels raw34572step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw34573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34573step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34573 raw34573Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw34573 raw34573Labels = mixedMoment B raw34573step0 raw34573step0Labels := by
      have ha : raw34573step0 = (fun i j => raw34573 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34573step0 raw34573; decide +kernel
      have hl : raw34573step0Labels = raw34573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34573 raw34573Labels permutation172 permutation3
    mixedMoment B raw34573step0 raw34573step0Labels = mixedMoment B raw34573step1 raw34573step1Labels := by
      have ha : raw34573step1 = raw34573step0 := by apply Matrix.ext; unfold raw34573step1 raw34573step0; decide +kernel
      have hl : raw34573step0Labels = labelEmbedding6 ∘ raw34573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34573step0 raw34573step0Labels raw34573step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw34574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34574step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34574 raw34574Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw34574 raw34574Labels = mixedMoment B raw34574step0 raw34574step0Labels := by
      have ha : raw34574step0 = (fun i j => raw34574 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34574step0 raw34574; decide +kernel
      have hl : raw34574step0Labels = raw34574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34574 raw34574Labels permutation172 permutation3
    mixedMoment B raw34574step0 raw34574step0Labels = mixedMoment B raw34574step1 raw34574step1Labels := by
      have ha : raw34574step1 = raw34574step0 := by apply Matrix.ext; unfold raw34574step1 raw34574step0; decide +kernel
      have hl : raw34574step0Labels = labelEmbedding6 ∘ raw34574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34574step0 raw34574step0Labels raw34574step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw34575 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw34575step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34575step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34575step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34575 raw34575Labels = mixedMoment B node5212 node5212Labels := by
  calc
    mixedMoment B raw34575 raw34575Labels = mixedMoment B raw34575step0 raw34575step0Labels := by
      have ha : raw34575step0 = (fun i j => raw34575 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34575step0 raw34575; decide +kernel
      have hl : raw34575step0Labels = raw34575Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34575 raw34575Labels permutation265 permutation5
    mixedMoment B raw34575step0 raw34575step0Labels = mixedMoment B raw34575step1 raw34575step1Labels := by
      have ha : raw34575step1 = -raw34575step0 := by apply Matrix.ext; change ∀ i j, raw34575step1 i j = -(raw34575step0 i j); unfold raw34575step1 raw34575step0; decide +kernel
      have hl : raw34575step1Labels = raw34575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34575step1 raw34575step1Labels = mixedMoment B raw34575step2 raw34575step2Labels := by
      have ha : raw34575step2 = raw34575step1 := by apply Matrix.ext; unfold raw34575step2 raw34575step1; decide +kernel
      have hl : raw34575step1Labels = labelEmbedding8 ∘ raw34575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34575step1 raw34575step1Labels raw34575step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5212 node5212Labels := by rfl

def raw34576 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34576step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34576 raw34576Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34576 raw34576Labels = mixedMoment B raw34576step0 raw34576step0Labels := by
      have ha : raw34576step0 = (fun i j => raw34576 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34576step0 raw34576; decide +kernel
      have hl : raw34576step0Labels = raw34576Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34576 raw34576Labels permutation161 permutation7
    mixedMoment B raw34576step0 raw34576step0Labels = mixedMoment B raw34576step1 raw34576step1Labels := by
      have ha : raw34576step1 = raw34576step0 := by apply Matrix.ext; unfold raw34576step1 raw34576step0; decide +kernel
      have hl : raw34576step0Labels = labelEmbedding10 ∘ raw34576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34576step0 raw34576step0Labels raw34576step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34577step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34577 raw34577Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34577 raw34577Labels = mixedMoment B raw34577step0 raw34577step0Labels := by
      have ha : raw34577step0 = (fun i j => raw34577 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34577step0 raw34577; decide +kernel
      have hl : raw34577step0Labels = raw34577Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34577 raw34577Labels permutation155 permutation7
    mixedMoment B raw34577step0 raw34577step0Labels = mixedMoment B raw34577step1 raw34577step1Labels := by
      have ha : raw34577step1 = raw34577step0 := by apply Matrix.ext; unfold raw34577step1 raw34577step0; decide +kernel
      have hl : raw34577step0Labels = labelEmbedding10 ∘ raw34577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34577step0 raw34577step0Labels raw34577step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34578step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34578 raw34578Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34578 raw34578Labels = mixedMoment B raw34578step0 raw34578step0Labels := by
      have ha : raw34578step0 = (fun i j => raw34578 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34578step0 raw34578; decide +kernel
      have hl : raw34578step0Labels = raw34578Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34578 raw34578Labels permutation153 permutation7
    mixedMoment B raw34578step0 raw34578step0Labels = mixedMoment B raw34578step1 raw34578step1Labels := by
      have ha : raw34578step1 = raw34578step0 := by apply Matrix.ext; unfold raw34578step1 raw34578step0; decide +kernel
      have hl : raw34578step0Labels = labelEmbedding10 ∘ raw34578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34578step0 raw34578step0Labels raw34578step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34579 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34579step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34579 raw34579Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34579 raw34579Labels = mixedMoment B raw34579step0 raw34579step0Labels := by
      have ha : raw34579step0 = (fun i j => raw34579 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34579step0 raw34579; decide +kernel
      have hl : raw34579step0Labels = raw34579Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34579 raw34579Labels permutation152 permutation7
    mixedMoment B raw34579step0 raw34579step0Labels = mixedMoment B raw34579step1 raw34579step1Labels := by
      have ha : raw34579step1 = raw34579step0 := by apply Matrix.ext; unfold raw34579step1 raw34579step0; decide +kernel
      have hl : raw34579step0Labels = labelEmbedding10 ∘ raw34579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34579step0 raw34579step0Labels raw34579step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34580 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34580step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw34580step0Labels : Fin 2 → Fin 3 := ![1, 2]

def raw34580step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw34580step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw34580step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw34580step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34580 raw34580Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw34580 raw34580Labels = mixedMoment B raw34580step0 raw34580step0Labels := by
      have hz : ∀ i, raw34580 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw34580step0 = (fun i j => raw34580 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw34580step0 raw34580; decide +kernel
      have hl : raw34580step0Labels = (fun j => raw34580Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34580 raw34580Labels permutation2 hz
    mixedMoment B raw34580step0 raw34580step0Labels = mixedMoment B raw34580step1 raw34580step1Labels := by
      have ha : raw34580step1 = -raw34580step0 := by apply Matrix.ext; change ∀ i j, raw34580step1 i j = -(raw34580step0 i j); unfold raw34580step1 raw34580step0; decide +kernel
      have hl : raw34580step1Labels = raw34580step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34580step1 raw34580step1Labels = mixedMoment B raw34580step2 raw34580step2Labels := by
      have ha : raw34580step2 = raw34580step1 := by apply Matrix.ext; unfold raw34580step2 raw34580step1; decide +kernel
      have hl : raw34580step1Labels = labelEmbedding3 ∘ raw34580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34580step1 raw34580step1Labels raw34580step2Labels labelEmbedding3 hl
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw34581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34581step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34581 raw34581Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw34581 raw34581Labels = mixedMoment B raw34581step0 raw34581step0Labels := by
      have ha : raw34581step0 = (fun i j => raw34581 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34581step0 raw34581; decide +kernel
      have hl : raw34581step0Labels = raw34581Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34581 raw34581Labels permutation152 permutation6
    mixedMoment B raw34581step0 raw34581step0Labels = mixedMoment B raw34581step1 raw34581step1Labels := by
      have ha : raw34581step1 = raw34581step0 := by apply Matrix.ext; unfold raw34581step1 raw34581step0; decide +kernel
      have hl : raw34581step0Labels = labelEmbedding9 ∘ raw34581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34581step0 raw34581step0Labels raw34581step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw34582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34582step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34582 raw34582Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw34582 raw34582Labels = mixedMoment B raw34582step0 raw34582step0Labels := by
      have ha : raw34582step0 = (fun i j => raw34582 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34582step0 raw34582; decide +kernel
      have hl : raw34582step0Labels = raw34582Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34582 raw34582Labels permutation158 permutation6
    mixedMoment B raw34582step0 raw34582step0Labels = mixedMoment B raw34582step1 raw34582step1Labels := by
      have ha : raw34582step1 = raw34582step0 := by apply Matrix.ext; unfold raw34582step1 raw34582step0; decide +kernel
      have hl : raw34582step0Labels = labelEmbedding9 ∘ raw34582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34582step0 raw34582step0Labels raw34582step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw34583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34583step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34583 raw34583Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw34583 raw34583Labels = mixedMoment B raw34583step0 raw34583step0Labels := by
      have ha : raw34583step0 = (fun i j => raw34583 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34583step0 raw34583; decide +kernel
      have hl : raw34583step0Labels = raw34583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34583 raw34583Labels permutation164 permutation6
    mixedMoment B raw34583step0 raw34583step0Labels = mixedMoment B raw34583step1 raw34583step1Labels := by
      have ha : raw34583step1 = raw34583step0 := by apply Matrix.ext; unfold raw34583step1 raw34583step0; decide +kernel
      have hl : raw34583step0Labels = labelEmbedding9 ∘ raw34583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34583step0 raw34583step0Labels raw34583step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw34584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34584step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34584step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34584step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34584 raw34584Labels = mixedMoment B node4647 node4647Labels := by
  calc
    mixedMoment B raw34584 raw34584Labels = mixedMoment B raw34584step0 raw34584step0Labels := by
      have ha : raw34584step0 = (fun i j => raw34584 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34584step0 raw34584; decide +kernel
      have hl : raw34584step0Labels = raw34584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34584 raw34584Labels permutation161 permutation4
    mixedMoment B raw34584step0 raw34584step0Labels = mixedMoment B raw34584step1 raw34584step1Labels := by
      have ha : raw34584step1 = -raw34584step0 := by apply Matrix.ext; change ∀ i j, raw34584step1 i j = -(raw34584step0 i j); unfold raw34584step1 raw34584step0; decide +kernel
      have hl : raw34584step1Labels = raw34584step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34584step1 raw34584step1Labels = mixedMoment B raw34584step2 raw34584step2Labels := by
      have ha : raw34584step2 = raw34584step1 := by apply Matrix.ext; unfold raw34584step2 raw34584step1; decide +kernel
      have hl : raw34584step1Labels = labelEmbedding7 ∘ raw34584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34584step1 raw34584step1Labels raw34584step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4647 node4647Labels := by rfl

def raw34585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw34585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34585 raw34585Labels = mixedMoment B node4980 node4980Labels := by
  calc
    mixedMoment B raw34585 raw34585Labels = mixedMoment B raw34585step0 raw34585step0Labels := by
      have ha : raw34585step0 = (fun i j => raw34585 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34585step0 raw34585; decide +kernel
      have hl : raw34585step0Labels = raw34585Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34585 raw34585Labels permutation274 permutation5
    mixedMoment B raw34585step0 raw34585step0Labels = mixedMoment B raw34585step1 raw34585step1Labels := by
      have ha : raw34585step1 = -raw34585step0 := by apply Matrix.ext; change ∀ i j, raw34585step1 i j = -(raw34585step0 i j); unfold raw34585step1 raw34585step0; decide +kernel
      have hl : raw34585step1Labels = raw34585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34585step1 raw34585step1Labels = mixedMoment B raw34585step2 raw34585step2Labels := by
      have ha : raw34585step2 = raw34585step1 := by apply Matrix.ext; unfold raw34585step2 raw34585step1; decide +kernel
      have hl : raw34585step1Labels = labelEmbedding8 ∘ raw34585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34585step1 raw34585step1Labels raw34585step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw34586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34586step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34586 raw34586Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34586 raw34586Labels = mixedMoment B raw34586step0 raw34586step0Labels := by
      have ha : raw34586step0 = (fun i j => raw34586 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34586step0 raw34586; decide +kernel
      have hl : raw34586step0Labels = raw34586Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34586 raw34586Labels permutation161 permutation6
    mixedMoment B raw34586step0 raw34586step0Labels = mixedMoment B raw34586step1 raw34586step1Labels := by
      have ha : raw34586step1 = raw34586step0 := by apply Matrix.ext; unfold raw34586step1 raw34586step0; decide +kernel
      have hl : raw34586step0Labels = labelEmbedding9 ∘ raw34586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34586step0 raw34586step0Labels raw34586step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34587step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34587 raw34587Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34587 raw34587Labels = mixedMoment B raw34587step0 raw34587step0Labels := by
      have ha : raw34587step0 = (fun i j => raw34587 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34587step0 raw34587; decide +kernel
      have hl : raw34587step0Labels = raw34587Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34587 raw34587Labels permutation167 permutation6
    mixedMoment B raw34587step0 raw34587step0Labels = mixedMoment B raw34587step1 raw34587step1Labels := by
      have ha : raw34587step1 = raw34587step0 := by apply Matrix.ext; unfold raw34587step1 raw34587step0; decide +kernel
      have hl : raw34587step0Labels = labelEmbedding9 ∘ raw34587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34587step0 raw34587step0Labels raw34587step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34588step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34588 raw34588Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34588 raw34588Labels = mixedMoment B raw34588step0 raw34588step0Labels := by
      have ha : raw34588step0 = (fun i j => raw34588 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34588step0 raw34588; decide +kernel
      have hl : raw34588step0Labels = raw34588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34588 raw34588Labels permutation173 permutation6
    mixedMoment B raw34588step0 raw34588step0Labels = mixedMoment B raw34588step1 raw34588step1Labels := by
      have ha : raw34588step1 = raw34588step0 := by apply Matrix.ext; unfold raw34588step1 raw34588step0; decide +kernel
      have hl : raw34588step0Labels = labelEmbedding9 ∘ raw34588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34588step0 raw34588step0Labels raw34588step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34589step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34589step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34589step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34589 raw34589Labels = mixedMoment B node4647 node4647Labels := by
  calc
    mixedMoment B raw34589 raw34589Labels = mixedMoment B raw34589step0 raw34589step0Labels := by
      have ha : raw34589step0 = (fun i j => raw34589 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34589step0 raw34589; decide +kernel
      have hl : raw34589step0Labels = raw34589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34589 raw34589Labels permutation155 permutation4
    mixedMoment B raw34589step0 raw34589step0Labels = mixedMoment B raw34589step1 raw34589step1Labels := by
      have ha : raw34589step1 = -raw34589step0 := by apply Matrix.ext; change ∀ i j, raw34589step1 i j = -(raw34589step0 i j); unfold raw34589step1 raw34589step0; decide +kernel
      have hl : raw34589step1Labels = raw34589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34589step1 raw34589step1Labels = mixedMoment B raw34589step2 raw34589step2Labels := by
      have ha : raw34589step2 = raw34589step1 := by apply Matrix.ext; unfold raw34589step2 raw34589step1; decide +kernel
      have hl : raw34589step1Labels = labelEmbedding7 ∘ raw34589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34589step1 raw34589step1Labels raw34589step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4647 node4647Labels := by rfl

def raw34590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw34590step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34590step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34590step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34590 raw34590Labels = mixedMoment B node4980 node4980Labels := by
  calc
    mixedMoment B raw34590 raw34590Labels = mixedMoment B raw34590step0 raw34590step0Labels := by
      have ha : raw34590step0 = (fun i j => raw34590 (permutation268 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34590step0 raw34590; decide +kernel
      have hl : raw34590step0Labels = raw34590Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34590 raw34590Labels permutation268 permutation5
    mixedMoment B raw34590step0 raw34590step0Labels = mixedMoment B raw34590step1 raw34590step1Labels := by
      have ha : raw34590step1 = -raw34590step0 := by apply Matrix.ext; change ∀ i j, raw34590step1 i j = -(raw34590step0 i j); unfold raw34590step1 raw34590step0; decide +kernel
      have hl : raw34590step1Labels = raw34590step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34590step1 raw34590step1Labels = mixedMoment B raw34590step2 raw34590step2Labels := by
      have ha : raw34590step2 = raw34590step1 := by apply Matrix.ext; unfold raw34590step2 raw34590step1; decide +kernel
      have hl : raw34590step1Labels = labelEmbedding8 ∘ raw34590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34590step1 raw34590step1Labels raw34590step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw34591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw34591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34591step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34591 raw34591Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34591 raw34591Labels = mixedMoment B raw34591step0 raw34591step0Labels := by
      have ha : raw34591step0 = (fun i j => raw34591 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34591step0 raw34591; decide +kernel
      have hl : raw34591step0Labels = raw34591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34591 raw34591Labels permutation155 permutation6
    mixedMoment B raw34591step0 raw34591step0Labels = mixedMoment B raw34591step1 raw34591step1Labels := by
      have ha : raw34591step1 = raw34591step0 := by apply Matrix.ext; unfold raw34591step1 raw34591step0; decide +kernel
      have hl : raw34591step0Labels = labelEmbedding9 ∘ raw34591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34591step0 raw34591step0Labels raw34591step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34592step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34592 raw34592Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34592 raw34592Labels = mixedMoment B raw34592step0 raw34592step0Labels := by
      have ha : raw34592step0 = (fun i j => raw34592 (permutation165 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34592step0 raw34592; decide +kernel
      have hl : raw34592step0Labels = raw34592Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34592 raw34592Labels permutation165 permutation6
    mixedMoment B raw34592step0 raw34592step0Labels = mixedMoment B raw34592step1 raw34592step1Labels := by
      have ha : raw34592step1 = raw34592step0 := by apply Matrix.ext; unfold raw34592step1 raw34592step0; decide +kernel
      have hl : raw34592step0Labels = labelEmbedding9 ∘ raw34592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34592step0 raw34592step0Labels raw34592step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34593step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34593 raw34593Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34593 raw34593Labels = mixedMoment B raw34593step0 raw34593step0Labels := by
      have ha : raw34593step0 = (fun i j => raw34593 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34593step0 raw34593; decide +kernel
      have hl : raw34593step0Labels = raw34593Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34593 raw34593Labels permutation171 permutation6
    mixedMoment B raw34593step0 raw34593step0Labels = mixedMoment B raw34593step1 raw34593step1Labels := by
      have ha : raw34593step1 = raw34593step0 := by apply Matrix.ext; unfold raw34593step1 raw34593step0; decide +kernel
      have hl : raw34593step0Labels = labelEmbedding9 ∘ raw34593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34593step0 raw34593step0Labels raw34593step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw34594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34594step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34594step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34594step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34594step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34594 raw34594Labels = mixedMoment B node4647 node4647Labels := by
  calc
    mixedMoment B raw34594 raw34594Labels = mixedMoment B raw34594step0 raw34594step0Labels := by
      have ha : raw34594step0 = (fun i j => raw34594 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34594step0 raw34594; decide +kernel
      have hl : raw34594step0Labels = raw34594Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34594 raw34594Labels permutation153 permutation4
    mixedMoment B raw34594step0 raw34594step0Labels = mixedMoment B raw34594step1 raw34594step1Labels := by
      have ha : raw34594step1 = -raw34594step0 := by apply Matrix.ext; change ∀ i j, raw34594step1 i j = -(raw34594step0 i j); unfold raw34594step1 raw34594step0; decide +kernel
      have hl : raw34594step1Labels = raw34594step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34594step1 raw34594step1Labels = mixedMoment B raw34594step2 raw34594step2Labels := by
      have ha : raw34594step2 = raw34594step1 := by apply Matrix.ext; unfold raw34594step2 raw34594step1; decide +kernel
      have hl : raw34594step1Labels = labelEmbedding7 ∘ raw34594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34594step1 raw34594step1Labels raw34594step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4647 node4647Labels := by rfl

def raw34595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw34595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw34595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34595step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34595 raw34595Labels = mixedMoment B node4980 node4980Labels := by
  calc
    mixedMoment B raw34595 raw34595Labels = mixedMoment B raw34595step0 raw34595step0Labels := by
      have ha : raw34595step0 = (fun i j => raw34595 (permutation266 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34595step0 raw34595; decide +kernel
      have hl : raw34595step0Labels = raw34595Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34595 raw34595Labels permutation266 permutation5
    mixedMoment B raw34595step0 raw34595step0Labels = mixedMoment B raw34595step1 raw34595step1Labels := by
      have ha : raw34595step1 = -raw34595step0 := by apply Matrix.ext; change ∀ i j, raw34595step1 i j = -(raw34595step0 i j); unfold raw34595step1 raw34595step0; decide +kernel
      have hl : raw34595step1Labels = raw34595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34595step1 raw34595step1Labels = mixedMoment B raw34595step2 raw34595step2Labels := by
      have ha : raw34595step2 = raw34595step1 := by apply Matrix.ext; unfold raw34595step2 raw34595step1; decide +kernel
      have hl : raw34595step1Labels = labelEmbedding8 ∘ raw34595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34595step1 raw34595step1Labels raw34595step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw34596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw34596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34596step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34596 raw34596Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34596 raw34596Labels = mixedMoment B raw34596step0 raw34596step0Labels := by
      have ha : raw34596step0 = (fun i j => raw34596 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34596step0 raw34596; decide +kernel
      have hl : raw34596step0Labels = raw34596Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34596 raw34596Labels permutation153 permutation6
    mixedMoment B raw34596step0 raw34596step0Labels = mixedMoment B raw34596step1 raw34596step1Labels := by
      have ha : raw34596step1 = raw34596step0 := by apply Matrix.ext; unfold raw34596step1 raw34596step0; decide +kernel
      have hl : raw34596step0Labels = labelEmbedding9 ∘ raw34596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34596step0 raw34596step0Labels raw34596step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1]]
def raw34597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34597step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34597 raw34597Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34597 raw34597Labels = mixedMoment B raw34597step0 raw34597step0Labels := by
      have ha : raw34597step0 = (fun i j => raw34597 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34597step0 raw34597; decide +kernel
      have hl : raw34597step0Labels = raw34597Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34597 raw34597Labels permutation159 permutation6
    mixedMoment B raw34597step0 raw34597step0Labels = mixedMoment B raw34597step1 raw34597step1Labels := by
      have ha : raw34597step1 = raw34597step0 := by apply Matrix.ext; unfold raw34597step1 raw34597step0; decide +kernel
      have hl : raw34597step0Labels = labelEmbedding9 ∘ raw34597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34597step0 raw34597step0Labels raw34597step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw34598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34598step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34598 raw34598Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34598 raw34598Labels = mixedMoment B raw34598step0 raw34598step0Labels := by
      have ha : raw34598step0 = (fun i j => raw34598 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34598step0 raw34598; decide +kernel
      have hl : raw34598step0Labels = raw34598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34598 raw34598Labels permutation170 permutation6
    mixedMoment B raw34598step0 raw34598step0Labels = mixedMoment B raw34598step1 raw34598step1Labels := by
      have ha : raw34598step1 = raw34598step0 := by apply Matrix.ext; unfold raw34598step1 raw34598step0; decide +kernel
      have hl : raw34598step0Labels = labelEmbedding9 ∘ raw34598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34598step0 raw34598step0Labels raw34598step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw34599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34599step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34599step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34599step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34599 raw34599Labels = mixedMoment B node4647 node4647Labels := by
  calc
    mixedMoment B raw34599 raw34599Labels = mixedMoment B raw34599step0 raw34599step0Labels := by
      have ha : raw34599step0 = (fun i j => raw34599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34599step0 raw34599; decide +kernel
      have hl : raw34599step0Labels = raw34599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34599 raw34599Labels permutation152 permutation4
    mixedMoment B raw34599step0 raw34599step0Labels = mixedMoment B raw34599step1 raw34599step1Labels := by
      have ha : raw34599step1 = -raw34599step0 := by apply Matrix.ext; change ∀ i j, raw34599step1 i j = -(raw34599step0 i j); unfold raw34599step1 raw34599step0; decide +kernel
      have hl : raw34599step1Labels = raw34599step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34599step1 raw34599step1Labels = mixedMoment B raw34599step2 raw34599step2Labels := by
      have ha : raw34599step2 = raw34599step1 := by apply Matrix.ext; unfold raw34599step2 raw34599step1; decide +kernel
      have hl : raw34599step1Labels = labelEmbedding7 ∘ raw34599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34599step1 raw34599step1Labels raw34599step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4647 node4647Labels := by rfl

def raw34600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw34600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw34600step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34600step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34600 raw34600Labels = mixedMoment B node4980 node4980Labels := by
  calc
    mixedMoment B raw34600 raw34600Labels = mixedMoment B raw34600step0 raw34600step0Labels := by
      have ha : raw34600step0 = (fun i j => raw34600 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34600step0 raw34600; decide +kernel
      have hl : raw34600step0Labels = raw34600Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34600 raw34600Labels permutation265 permutation5
    mixedMoment B raw34600step0 raw34600step0Labels = mixedMoment B raw34600step1 raw34600step1Labels := by
      have ha : raw34600step1 = -raw34600step0 := by apply Matrix.ext; change ∀ i j, raw34600step1 i j = -(raw34600step0 i j); unfold raw34600step1 raw34600step0; decide +kernel
      have hl : raw34600step1Labels = raw34600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34600step1 raw34600step1Labels = mixedMoment B raw34600step2 raw34600step2Labels := by
      have ha : raw34600step2 = raw34600step1 := by apply Matrix.ext; unfold raw34600step2 raw34600step1; decide +kernel
      have hl : raw34600step1Labels = labelEmbedding8 ∘ raw34600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34600step1 raw34600step1Labels raw34600step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4980 node4980Labels := by rfl

def raw34601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw34601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34601step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34601 raw34601Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34601 raw34601Labels = mixedMoment B raw34601step0 raw34601step0Labels := by
      have ha : raw34601step0 = (fun i j => raw34601 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34601step0 raw34601; decide +kernel
      have hl : raw34601step0Labels = raw34601Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34601 raw34601Labels permutation152 permutation6
    mixedMoment B raw34601step0 raw34601step0Labels = mixedMoment B raw34601step1 raw34601step1Labels := by
      have ha : raw34601step1 = raw34601step0 := by apply Matrix.ext; unfold raw34601step1 raw34601step0; decide +kernel
      have hl : raw34601step0Labels = labelEmbedding9 ∘ raw34601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34601step0 raw34601step0Labels raw34601step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw34602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34602step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34602 raw34602Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34602 raw34602Labels = mixedMoment B raw34602step0 raw34602step0Labels := by
      have ha : raw34602step0 = (fun i j => raw34602 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34602step0 raw34602; decide +kernel
      have hl : raw34602step0Labels = raw34602Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34602 raw34602Labels permutation158 permutation6
    mixedMoment B raw34602step0 raw34602step0Labels = mixedMoment B raw34602step1 raw34602step1Labels := by
      have ha : raw34602step1 = raw34602step0 := by apply Matrix.ext; unfold raw34602step1 raw34602step0; decide +kernel
      have hl : raw34602step0Labels = labelEmbedding9 ∘ raw34602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34602step0 raw34602step0Labels raw34602step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw34603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34603step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34603 raw34603Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw34603 raw34603Labels = mixedMoment B raw34603step0 raw34603step0Labels := by
      have ha : raw34603step0 = (fun i j => raw34603 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34603step0 raw34603; decide +kernel
      have hl : raw34603step0Labels = raw34603Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34603 raw34603Labels permutation164 permutation6
    mixedMoment B raw34603step0 raw34603step0Labels = mixedMoment B raw34603step1 raw34603step1Labels := by
      have ha : raw34603step1 = raw34603step0 := by apply Matrix.ext; unfold raw34603step1 raw34603step0; decide +kernel
      have hl : raw34603step0Labels = labelEmbedding9 ∘ raw34603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34603step0 raw34603step0Labels raw34603step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw34604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34604step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34604 raw34604Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw34604 raw34604Labels = mixedMoment B raw34604step0 raw34604step0Labels := by
      have ha : raw34604step0 = (fun i j => raw34604 (permutation295 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34604step0 raw34604; decide +kernel
      have hl : raw34604step0Labels = raw34604Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34604 raw34604Labels permutation295 permutation5
    mixedMoment B raw34604step0 raw34604step0Labels = mixedMoment B raw34604step1 raw34604step1Labels := by
      have ha : raw34604step1 = -raw34604step0 := by apply Matrix.ext; change ∀ i j, raw34604step1 i j = -(raw34604step0 i j); unfold raw34604step1 raw34604step0; decide +kernel
      have hl : raw34604step1Labels = raw34604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34604step1 raw34604step1Labels = mixedMoment B raw34604step2 raw34604step2Labels := by
      have ha : raw34604step2 = raw34604step1 := by apply Matrix.ext; unfold raw34604step2 raw34604step1; decide +kernel
      have hl : raw34604step1Labels = labelEmbedding8 ∘ raw34604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34604step1 raw34604step1Labels raw34604step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

def raw34605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34605step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34605 raw34605Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw34605 raw34605Labels = mixedMoment B raw34605step0 raw34605step0Labels := by
      have ha : raw34605step0 = (fun i j => raw34605 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34605step0 raw34605; decide +kernel
      have hl : raw34605step0Labels = raw34605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34605 raw34605Labels permutation241 permutation7
    mixedMoment B raw34605step0 raw34605step0Labels = mixedMoment B raw34605step1 raw34605step1Labels := by
      have ha : raw34605step1 = -raw34605step0 := by apply Matrix.ext; change ∀ i j, raw34605step1 i j = -(raw34605step0 i j); unfold raw34605step1 raw34605step0; decide +kernel
      have hl : raw34605step1Labels = raw34605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34605step1 raw34605step1Labels = mixedMoment B raw34605step2 raw34605step2Labels := by
      have ha : raw34605step2 = raw34605step1 := by apply Matrix.ext; unfold raw34605step2 raw34605step1; decide +kernel
      have hl : raw34605step1Labels = labelEmbedding10 ∘ raw34605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34605step1 raw34605step1Labels raw34605step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw34606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34606step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34606step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34606 raw34606Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw34606 raw34606Labels = mixedMoment B raw34606step0 raw34606step0Labels := by
      have hz : ∀ j, raw34606 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34606step0 = (fun i j => raw34606 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34606step0 raw34606; decide +kernel
      have hl : raw34606step0Labels = raw34606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34606 raw34606Labels permutation520 hz
    mixedMoment B raw34606step0 raw34606step0Labels = mixedMoment B raw34606step1 raw34606step1Labels := by
      have ha : raw34606step1 = (fun i j => raw34606step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34606step1 raw34606step0; decide +kernel
      have hl : raw34606step1Labels = raw34606step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34606step0 raw34606step0Labels permutation50 permutation7
    mixedMoment B raw34606step1 raw34606step1Labels = mixedMoment B raw34606step2 raw34606step2Labels := by
      have ha : raw34606step2 = -raw34606step1 := by apply Matrix.ext; change ∀ i j, raw34606step2 i j = -(raw34606step1 i j); unfold raw34606step2 raw34606step1; decide +kernel
      have hl : raw34606step2Labels = raw34606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34606step2 raw34606step2Labels = mixedMoment B raw34606step3 raw34606step3Labels := by
      have ha : raw34606step3 = raw34606step2 := by apply Matrix.ext; unfold raw34606step3 raw34606step2; decide +kernel
      have hl : raw34606step2Labels = labelEmbedding10 ∘ raw34606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34606step2 raw34606step2Labels raw34606step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw34607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34607step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34607 raw34607Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw34607 raw34607Labels = mixedMoment B raw34607step0 raw34607step0Labels := by
      have hz : ∀ j, raw34607 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34607step0 = (fun i j => raw34607 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34607step0 raw34607; decide +kernel
      have hl : raw34607step0Labels = raw34607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34607 raw34607Labels permutation590 hz
    mixedMoment B raw34607step0 raw34607step0Labels = mixedMoment B raw34607step1 raw34607step1Labels := by
      have ha : raw34607step1 = (fun i j => raw34607step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34607step1 raw34607step0; decide +kernel
      have hl : raw34607step1Labels = raw34607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34607step0 raw34607step0Labels permutation50 permutation7
    mixedMoment B raw34607step1 raw34607step1Labels = mixedMoment B raw34607step2 raw34607step2Labels := by
      have ha : raw34607step2 = -raw34607step1 := by apply Matrix.ext; change ∀ i j, raw34607step2 i j = -(raw34607step1 i j); unfold raw34607step2 raw34607step1; decide +kernel
      have hl : raw34607step2Labels = raw34607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34607step2 raw34607step2Labels = mixedMoment B raw34607step3 raw34607step3Labels := by
      have ha : raw34607step3 = raw34607step2 := by apply Matrix.ext; unfold raw34607step3 raw34607step2; decide +kernel
      have hl : raw34607step2Labels = labelEmbedding10 ∘ raw34607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34607step2 raw34607step2Labels raw34607step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw34608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34608 raw34608Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw34608 raw34608Labels = mixedMoment B raw34608step0 raw34608step0Labels := by
      have ha : raw34608step0 = (fun i j => raw34608 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34608step0 raw34608; decide +kernel
      have hl : raw34608step0Labels = raw34608Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34608 raw34608Labels permutation169 permutation2
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw34609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34609 raw34609Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw34609 raw34609Labels = mixedMoment B raw34609step0 raw34609step0Labels := by
      have ha : raw34609step0 = (fun i j => raw34609 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34609step0 raw34609; decide +kernel
      have hl : raw34609step0Labels = raw34609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34609 raw34609Labels permutation161 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw34610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34610 raw34610Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw34610 raw34610Labels = mixedMoment B raw34610step0 raw34610step0Labels := by
      have hz : ∀ j, raw34610 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34610step0 = (fun i j => raw34610 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34610step0 raw34610; decide +kernel
      have hl : raw34610step0Labels = raw34610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34610 raw34610Labels permutation520 hz
    mixedMoment B raw34610step0 raw34610step0Labels = mixedMoment B raw34610step1 raw34610step1Labels := by
      have ha : raw34610step1 = (fun i j => raw34610step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34610step1 raw34610step0; decide +kernel
      have hl : raw34610step1Labels = raw34610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34610step0 raw34610step0Labels permutation37 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw34611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34611 raw34611Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw34611 raw34611Labels = mixedMoment B raw34611step0 raw34611step0Labels := by
      have hz : ∀ j, raw34611 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34611step0 = (fun i j => raw34611 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34611step0 raw34611; decide +kernel
      have hl : raw34611step0Labels = raw34611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34611 raw34611Labels permutation590 hz
    mixedMoment B raw34611step0 raw34611step0Labels = mixedMoment B raw34611step1 raw34611step1Labels := by
      have ha : raw34611step1 = (fun i j => raw34611step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34611step1 raw34611step0; decide +kernel
      have hl : raw34611step1Labels = raw34611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34611step0 raw34611step0Labels permutation37 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw34612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34612 raw34612Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw34612 raw34612Labels = mixedMoment B raw34612step0 raw34612step0Labels := by
      have ha : raw34612step0 = (fun i j => raw34612 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34612step0 raw34612; decide +kernel
      have hl : raw34612step0Labels = raw34612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34612 raw34612Labels permutation168 permutation2
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw34613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34613 raw34613Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw34613 raw34613Labels = mixedMoment B raw34613step0 raw34613step0Labels := by
      have hz : ∀ j, raw34613 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34613step0 = (fun i j => raw34613 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34613step0 raw34613; decide +kernel
      have hl : raw34613step0Labels = raw34613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34613 raw34613Labels permutation520 hz
    mixedMoment B raw34613step0 raw34613step0Labels = mixedMoment B raw34613step1 raw34613step1Labels := by
      have ha : raw34613step1 = (fun i j => raw34613step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34613step1 raw34613step0; decide +kernel
      have hl : raw34613step1Labels = raw34613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34613step0 raw34613step0Labels permutation36 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw34614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34614 raw34614Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw34614 raw34614Labels = mixedMoment B raw34614step0 raw34614step0Labels := by
      have hz : ∀ j, raw34614 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34614step0 = (fun i j => raw34614 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34614step0 raw34614; decide +kernel
      have hl : raw34614step0Labels = raw34614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34614 raw34614Labels permutation590 hz
    mixedMoment B raw34614step0 raw34614step0Labels = mixedMoment B raw34614step1 raw34614step1Labels := by
      have ha : raw34614step1 = (fun i j => raw34614step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34614step1 raw34614step0; decide +kernel
      have hl : raw34614step1Labels = raw34614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34614step0 raw34614step0Labels permutation36 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw34615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34615 raw34615Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw34615 raw34615Labels = mixedMoment B raw34615step0 raw34615step0Labels := by
      have ha : raw34615step0 = (fun i j => raw34615 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34615step0 raw34615; decide +kernel
      have hl : raw34615step0Labels = raw34615Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34615 raw34615Labels permutation170 permutation2
    _ = mixedMoment B node4698 node4698Labels := by rfl

def raw34616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34616 raw34616Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw34616 raw34616Labels = mixedMoment B raw34616step0 raw34616step0Labels := by
      have ha : raw34616step0 = (fun i j => raw34616 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34616step0 raw34616; decide +kernel
      have hl : raw34616step0Labels = raw34616Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34616 raw34616Labels permutation162 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw34617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34617 raw34617Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw34617 raw34617Labels = mixedMoment B raw34617step0 raw34617step0Labels := by
      have hz : ∀ j, raw34617 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34617step0 = (fun i j => raw34617 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34617step0 raw34617; decide +kernel
      have hl : raw34617step0Labels = raw34617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34617 raw34617Labels permutation590 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw34618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34618 raw34618Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw34618 raw34618Labels = mixedMoment B raw34618step0 raw34618step0Labels := by
      have ha : raw34618step0 = (fun i j => raw34618 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34618step0 raw34618; decide +kernel
      have hl : raw34618step0Labels = raw34618Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34618 raw34618Labels permutation164 permutation2
    _ = mixedMoment B node4698 node4698Labels := by rfl

def raw34619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34619 raw34619Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw34619 raw34619Labels = mixedMoment B raw34619step0 raw34619step0Labels := by
      have hz : ∀ j, raw34619 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34619step0 = (fun i j => raw34619 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34619step0 raw34619; decide +kernel
      have hl : raw34619step0Labels = raw34619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34619 raw34619Labels permutation520 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw34620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34620 raw34620Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw34620 raw34620Labels = mixedMoment B raw34620step0 raw34620step0Labels := by
      have ha : raw34620step0 = (fun i j => raw34620 (permutation295 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34620step0 raw34620; decide +kernel
      have hl : raw34620step0Labels = raw34620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34620 raw34620Labels permutation295 permutation5
    mixedMoment B raw34620step0 raw34620step0Labels = mixedMoment B raw34620step1 raw34620step1Labels := by
      have ha : raw34620step1 = -raw34620step0 := by apply Matrix.ext; change ∀ i j, raw34620step1 i j = -(raw34620step0 i j); unfold raw34620step1 raw34620step0; decide +kernel
      have hl : raw34620step1Labels = raw34620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34620step1 raw34620step1Labels = mixedMoment B raw34620step2 raw34620step2Labels := by
      have ha : raw34620step2 = raw34620step1 := by apply Matrix.ext; unfold raw34620step2 raw34620step1; decide +kernel
      have hl : raw34620step1Labels = labelEmbedding1 ∘ raw34620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34620step1 raw34620step1Labels raw34620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw34621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34621 raw34621Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw34621 raw34621Labels = mixedMoment B raw34621step0 raw34621step0Labels := by
      have ha : raw34621step0 = (fun i j => raw34621 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34621step0 raw34621; decide +kernel
      have hl : raw34621step0Labels = raw34621Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34621 raw34621Labels permutation241 permutation7
    mixedMoment B raw34621step0 raw34621step0Labels = mixedMoment B raw34621step1 raw34621step1Labels := by
      have ha : raw34621step1 = -raw34621step0 := by apply Matrix.ext; change ∀ i j, raw34621step1 i j = -(raw34621step0 i j); unfold raw34621step1 raw34621step0; decide +kernel
      have hl : raw34621step1Labels = raw34621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34621step1 raw34621step1Labels = mixedMoment B raw34621step2 raw34621step2Labels := by
      have ha : raw34621step2 = raw34621step1 := by apply Matrix.ext; unfold raw34621step2 raw34621step1; decide +kernel
      have hl : raw34621step1Labels = labelEmbedding1 ∘ raw34621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34621step1 raw34621step1Labels raw34621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw34622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34622 raw34622Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw34622 raw34622Labels = mixedMoment B raw34622step0 raw34622step0Labels := by
      have hz : ∀ j, raw34622 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34622step0 = (fun i j => raw34622 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34622step0 raw34622; decide +kernel
      have hl : raw34622step0Labels = raw34622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34622 raw34622Labels permutation520 hz
    mixedMoment B raw34622step0 raw34622step0Labels = mixedMoment B raw34622step1 raw34622step1Labels := by
      have ha : raw34622step1 = (fun i j => raw34622step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34622step1 raw34622step0; decide +kernel
      have hl : raw34622step1Labels = raw34622step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34622step0 raw34622step0Labels permutation50 permutation7
    mixedMoment B raw34622step1 raw34622step1Labels = mixedMoment B raw34622step2 raw34622step2Labels := by
      have ha : raw34622step2 = -raw34622step1 := by apply Matrix.ext; change ∀ i j, raw34622step2 i j = -(raw34622step1 i j); unfold raw34622step2 raw34622step1; decide +kernel
      have hl : raw34622step2Labels = raw34622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34622step2 raw34622step2Labels = mixedMoment B raw34622step3 raw34622step3Labels := by
      have ha : raw34622step3 = raw34622step2 := by apply Matrix.ext; unfold raw34622step3 raw34622step2; decide +kernel
      have hl : raw34622step2Labels = labelEmbedding1 ∘ raw34622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34622step2 raw34622step2Labels raw34622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw34623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34623 raw34623Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw34623 raw34623Labels = mixedMoment B raw34623step0 raw34623step0Labels := by
      have hz : ∀ j, raw34623 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34623step0 = (fun i j => raw34623 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34623step0 raw34623; decide +kernel
      have hl : raw34623step0Labels = raw34623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34623 raw34623Labels permutation590 hz
    mixedMoment B raw34623step0 raw34623step0Labels = mixedMoment B raw34623step1 raw34623step1Labels := by
      have ha : raw34623step1 = (fun i j => raw34623step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34623step1 raw34623step0; decide +kernel
      have hl : raw34623step1Labels = raw34623step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34623step0 raw34623step0Labels permutation50 permutation7
    mixedMoment B raw34623step1 raw34623step1Labels = mixedMoment B raw34623step2 raw34623step2Labels := by
      have ha : raw34623step2 = -raw34623step1 := by apply Matrix.ext; change ∀ i j, raw34623step2 i j = -(raw34623step1 i j); unfold raw34623step2 raw34623step1; decide +kernel
      have hl : raw34623step2Labels = raw34623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34623step2 raw34623step2Labels = mixedMoment B raw34623step3 raw34623step3Labels := by
      have ha : raw34623step3 = raw34623step2 := by apply Matrix.ext; unfold raw34623step3 raw34623step2; decide +kernel
      have hl : raw34623step2Labels = labelEmbedding1 ∘ raw34623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34623step2 raw34623step2Labels raw34623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw34624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34624 raw34624Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw34624 raw34624Labels = mixedMoment B raw34624step0 raw34624step0Labels := by
      have ha : raw34624step0 = (fun i j => raw34624 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34624step0 raw34624; decide +kernel
      have hl : raw34624step0Labels = raw34624Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34624 raw34624Labels permutation241 permutation7
    mixedMoment B raw34624step0 raw34624step0Labels = mixedMoment B raw34624step1 raw34624step1Labels := by
      have ha : raw34624step1 = -raw34624step0 := by apply Matrix.ext; change ∀ i j, raw34624step1 i j = -(raw34624step0 i j); unfold raw34624step1 raw34624step0; decide +kernel
      have hl : raw34624step1Labels = raw34624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34624step1 raw34624step1Labels = mixedMoment B raw34624step2 raw34624step2Labels := by
      have ha : raw34624step2 = raw34624step1 := by apply Matrix.ext; unfold raw34624step2 raw34624step1; decide +kernel
      have hl : raw34624step1Labels = labelEmbedding1 ∘ raw34624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34624step1 raw34624step1Labels raw34624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw34625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34625 raw34625Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw34625 raw34625Labels = mixedMoment B raw34625step0 raw34625step0Labels := by
      have ha : raw34625step0 = (fun i j => raw34625 (permutation241 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34625step0 raw34625; decide +kernel
      have hl : raw34625step0Labels = raw34625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34625 raw34625Labels permutation241 permutation7
    mixedMoment B raw34625step0 raw34625step0Labels = mixedMoment B raw34625step1 raw34625step1Labels := by
      have ha : raw34625step1 = -raw34625step0 := by apply Matrix.ext; change ∀ i j, raw34625step1 i j = -(raw34625step0 i j); unfold raw34625step1 raw34625step0; decide +kernel
      have hl : raw34625step1Labels = raw34625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34625step1 raw34625step1Labels = mixedMoment B raw34625step2 raw34625step2Labels := by
      have ha : raw34625step2 = raw34625step1 := by apply Matrix.ext; unfold raw34625step2 raw34625step1; decide +kernel
      have hl : raw34625step1Labels = labelEmbedding1 ∘ raw34625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34625step1 raw34625step1Labels raw34625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw34626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34626 raw34626Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34626 raw34626Labels = mixedMoment B raw34626step0 raw34626step0Labels := by
      have hz : ∀ j, raw34626 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34626step0 = (fun i j => raw34626 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34626step0 raw34626; decide +kernel
      have hl : raw34626step0Labels = raw34626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34626 raw34626Labels permutation520 hz
    mixedMoment B raw34626step0 raw34626step0Labels = mixedMoment B raw34626step1 raw34626step1Labels := by
      have ha : raw34626step1 = (fun i j => raw34626step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34626step1 raw34626step0; decide +kernel
      have hl : raw34626step1Labels = raw34626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34626step0 raw34626step0Labels permutation51 permutation7
    mixedMoment B raw34626step1 raw34626step1Labels = mixedMoment B raw34626step2 raw34626step2Labels := by
      have ha : raw34626step2 = -raw34626step1 := by apply Matrix.ext; change ∀ i j, raw34626step2 i j = -(raw34626step1 i j); unfold raw34626step2 raw34626step1; decide +kernel
      have hl : raw34626step2Labels = raw34626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34626step2 raw34626step2Labels = mixedMoment B raw34626step3 raw34626step3Labels := by
      have ha : raw34626step3 = raw34626step2 := by apply Matrix.ext; unfold raw34626step3 raw34626step2; decide +kernel
      have hl : raw34626step2Labels = labelEmbedding1 ∘ raw34626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34626step2 raw34626step2Labels raw34626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw34627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34627 raw34627Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34627 raw34627Labels = mixedMoment B raw34627step0 raw34627step0Labels := by
      have hz : ∀ j, raw34627 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34627step0 = (fun i j => raw34627 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34627step0 raw34627; decide +kernel
      have hl : raw34627step0Labels = raw34627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34627 raw34627Labels permutation590 hz
    mixedMoment B raw34627step0 raw34627step0Labels = mixedMoment B raw34627step1 raw34627step1Labels := by
      have ha : raw34627step1 = (fun i j => raw34627step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34627step1 raw34627step0; decide +kernel
      have hl : raw34627step1Labels = raw34627step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34627step0 raw34627step0Labels permutation51 permutation7
    mixedMoment B raw34627step1 raw34627step1Labels = mixedMoment B raw34627step2 raw34627step2Labels := by
      have ha : raw34627step2 = -raw34627step1 := by apply Matrix.ext; change ∀ i j, raw34627step2 i j = -(raw34627step1 i j); unfold raw34627step2 raw34627step1; decide +kernel
      have hl : raw34627step2Labels = raw34627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34627step2 raw34627step2Labels = mixedMoment B raw34627step3 raw34627step3Labels := by
      have ha : raw34627step3 = raw34627step2 := by apply Matrix.ext; unfold raw34627step3 raw34627step2; decide +kernel
      have hl : raw34627step2Labels = labelEmbedding1 ∘ raw34627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34627step2 raw34627step2Labels raw34627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw34628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw34628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw34628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34628 raw34628Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw34628 raw34628Labels = mixedMoment B raw34628step0 raw34628step0Labels := by
      have ha : raw34628step0 = (fun i j => raw34628 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34628step0 raw34628; decide +kernel
      have hl : raw34628step0Labels = raw34628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34628 raw34628Labels permutation240 permutation7
    mixedMoment B raw34628step0 raw34628step0Labels = mixedMoment B raw34628step1 raw34628step1Labels := by
      have ha : raw34628step1 = -raw34628step0 := by apply Matrix.ext; change ∀ i j, raw34628step1 i j = -(raw34628step0 i j); unfold raw34628step1 raw34628step0; decide +kernel
      have hl : raw34628step1Labels = raw34628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34628step1 raw34628step1Labels = mixedMoment B raw34628step2 raw34628step2Labels := by
      have ha : raw34628step2 = raw34628step1 := by apply Matrix.ext; unfold raw34628step2 raw34628step1; decide +kernel
      have hl : raw34628step1Labels = labelEmbedding1 ∘ raw34628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34628step1 raw34628step1Labels raw34628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw34629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34629step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34629step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34629 raw34629Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34629 raw34629Labels = mixedMoment B raw34629step0 raw34629step0Labels := by
      have hz : ∀ j, raw34629 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34629step0 = (fun i j => raw34629 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34629step0 raw34629; decide +kernel
      have hl : raw34629step0Labels = raw34629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34629 raw34629Labels permutation520 hz
    mixedMoment B raw34629step0 raw34629step0Labels = mixedMoment B raw34629step1 raw34629step1Labels := by
      have ha : raw34629step1 = (fun i j => raw34629step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34629step1 raw34629step0; decide +kernel
      have hl : raw34629step1Labels = raw34629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34629step0 raw34629step0Labels permutation50 permutation7
    mixedMoment B raw34629step1 raw34629step1Labels = mixedMoment B raw34629step2 raw34629step2Labels := by
      have ha : raw34629step2 = -raw34629step1 := by apply Matrix.ext; change ∀ i j, raw34629step2 i j = -(raw34629step1 i j); unfold raw34629step2 raw34629step1; decide +kernel
      have hl : raw34629step2Labels = raw34629step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34629step2 raw34629step2Labels = mixedMoment B raw34629step3 raw34629step3Labels := by
      have ha : raw34629step3 = raw34629step2 := by apply Matrix.ext; unfold raw34629step3 raw34629step2; decide +kernel
      have hl : raw34629step2Labels = labelEmbedding1 ∘ raw34629step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34629step2 raw34629step2Labels raw34629step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw34630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34630 raw34630Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw34630 raw34630Labels = mixedMoment B raw34630step0 raw34630step0Labels := by
      have hz : ∀ j, raw34630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34630step0 = (fun i j => raw34630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34630step0 raw34630; decide +kernel
      have hl : raw34630step0Labels = raw34630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34630 raw34630Labels permutation590 hz
    mixedMoment B raw34630step0 raw34630step0Labels = mixedMoment B raw34630step1 raw34630step1Labels := by
      have ha : raw34630step1 = (fun i j => raw34630step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34630step1 raw34630step0; decide +kernel
      have hl : raw34630step1Labels = raw34630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34630step0 raw34630step0Labels permutation50 permutation7
    mixedMoment B raw34630step1 raw34630step1Labels = mixedMoment B raw34630step2 raw34630step2Labels := by
      have ha : raw34630step2 = -raw34630step1 := by apply Matrix.ext; change ∀ i j, raw34630step2 i j = -(raw34630step1 i j); unfold raw34630step2 raw34630step1; decide +kernel
      have hl : raw34630step2Labels = raw34630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34630step2 raw34630step2Labels = mixedMoment B raw34630step3 raw34630step3Labels := by
      have ha : raw34630step3 = raw34630step2 := by apply Matrix.ext; unfold raw34630step3 raw34630step2; decide +kernel
      have hl : raw34630step2Labels = labelEmbedding1 ∘ raw34630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34630step2 raw34630step2Labels raw34630step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw34631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34631 raw34631Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw34631 raw34631Labels = mixedMoment B raw34631step0 raw34631step0Labels := by
      have ha : raw34631step0 = (fun i j => raw34631 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34631step0 raw34631; decide +kernel
      have hl : raw34631step0Labels = raw34631Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34631 raw34631Labels permutation260 permutation7
    mixedMoment B raw34631step0 raw34631step0Labels = mixedMoment B raw34631step1 raw34631step1Labels := by
      have ha : raw34631step1 = -raw34631step0 := by apply Matrix.ext; change ∀ i j, raw34631step1 i j = -(raw34631step0 i j); unfold raw34631step1 raw34631step0; decide +kernel
      have hl : raw34631step1Labels = raw34631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34631step1 raw34631step1Labels = mixedMoment B raw34631step2 raw34631step2Labels := by
      have ha : raw34631step2 = raw34631step1 := by apply Matrix.ext; unfold raw34631step2 raw34631step1; decide +kernel
      have hl : raw34631step1Labels = labelEmbedding1 ∘ raw34631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34631step1 raw34631step1Labels raw34631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

def raw34632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw34632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34632step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw34632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34632 raw34632Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw34632 raw34632Labels = mixedMoment B raw34632step0 raw34632step0Labels := by
      have ha : raw34632step0 = (fun i j => raw34632 (permutation261 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34632step0 raw34632; decide +kernel
      have hl : raw34632step0Labels = raw34632Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34632 raw34632Labels permutation261 permutation7
    mixedMoment B raw34632step0 raw34632step0Labels = mixedMoment B raw34632step1 raw34632step1Labels := by
      have ha : raw34632step1 = -raw34632step0 := by apply Matrix.ext; change ∀ i j, raw34632step1 i j = -(raw34632step0 i j); unfold raw34632step1 raw34632step0; decide +kernel
      have hl : raw34632step1Labels = raw34632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34632step1 raw34632step1Labels = mixedMoment B raw34632step2 raw34632step2Labels := by
      have ha : raw34632step2 = raw34632step1 := by apply Matrix.ext; unfold raw34632step2 raw34632step1; decide +kernel
      have hl : raw34632step1Labels = labelEmbedding1 ∘ raw34632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34632step1 raw34632step1Labels raw34632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw34633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34633step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34633 raw34633Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw34633 raw34633Labels = mixedMoment B raw34633step0 raw34633step0Labels := by
      have hz : ∀ j, raw34633 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34633step0 = (fun i j => raw34633 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34633step0 raw34633; decide +kernel
      have hl : raw34633step0Labels = raw34633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34633 raw34633Labels permutation590 hz
    mixedMoment B raw34633step0 raw34633step0Labels = mixedMoment B raw34633step1 raw34633step1Labels := by
      have ha : raw34633step1 = (fun i j => raw34633step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34633step1 raw34633step0; decide +kernel
      have hl : raw34633step1Labels = raw34633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34633step0 raw34633step0Labels permutation50 permutation7
    mixedMoment B raw34633step1 raw34633step1Labels = mixedMoment B raw34633step2 raw34633step2Labels := by
      have ha : raw34633step2 = -raw34633step1 := by apply Matrix.ext; change ∀ i j, raw34633step2 i j = -(raw34633step1 i j); unfold raw34633step2 raw34633step1; decide +kernel
      have hl : raw34633step2Labels = raw34633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34633step2 raw34633step2Labels = mixedMoment B raw34633step3 raw34633step3Labels := by
      have ha : raw34633step3 = raw34633step2 := by apply Matrix.ext; unfold raw34633step3 raw34633step2; decide +kernel
      have hl : raw34633step2Labels = labelEmbedding1 ∘ raw34633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34633step2 raw34633step2Labels raw34633step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw34634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw34634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw34634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34634 raw34634Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw34634 raw34634Labels = mixedMoment B raw34634step0 raw34634step0Labels := by
      have ha : raw34634step0 = (fun i j => raw34634 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34634step0 raw34634; decide +kernel
      have hl : raw34634step0Labels = raw34634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34634 raw34634Labels permutation240 permutation7
    mixedMoment B raw34634step0 raw34634step0Labels = mixedMoment B raw34634step1 raw34634step1Labels := by
      have ha : raw34634step1 = -raw34634step0 := by apply Matrix.ext; change ∀ i j, raw34634step1 i j = -(raw34634step0 i j); unfold raw34634step1 raw34634step0; decide +kernel
      have hl : raw34634step1Labels = raw34634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34634step1 raw34634step1Labels = mixedMoment B raw34634step2 raw34634step2Labels := by
      have ha : raw34634step2 = raw34634step1 := by apply Matrix.ext; unfold raw34634step2 raw34634step1; decide +kernel
      have hl : raw34634step1Labels = labelEmbedding1 ∘ raw34634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34634step1 raw34634step1Labels raw34634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

def raw34635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34635 raw34635Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw34635 raw34635Labels = mixedMoment B raw34635step0 raw34635step0Labels := by
      have hz : ∀ j, raw34635 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34635step0 = (fun i j => raw34635 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34635step0 raw34635; decide +kernel
      have hl : raw34635step0Labels = raw34635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34635 raw34635Labels permutation520 hz
    mixedMoment B raw34635step0 raw34635step0Labels = mixedMoment B raw34635step1 raw34635step1Labels := by
      have ha : raw34635step1 = (fun i j => raw34635step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34635step1 raw34635step0; decide +kernel
      have hl : raw34635step1Labels = raw34635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34635step0 raw34635step0Labels permutation50 permutation7
    mixedMoment B raw34635step1 raw34635step1Labels = mixedMoment B raw34635step2 raw34635step2Labels := by
      have ha : raw34635step2 = -raw34635step1 := by apply Matrix.ext; change ∀ i j, raw34635step2 i j = -(raw34635step1 i j); unfold raw34635step2 raw34635step1; decide +kernel
      have hl : raw34635step2Labels = raw34635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34635step2 raw34635step2Labels = mixedMoment B raw34635step3 raw34635step3Labels := by
      have ha : raw34635step3 = raw34635step2 := by apply Matrix.ext; unfold raw34635step3 raw34635step2; decide +kernel
      have hl : raw34635step2Labels = labelEmbedding1 ∘ raw34635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34635step2 raw34635step2Labels raw34635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw34636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34636 raw34636Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw34636 raw34636Labels = mixedMoment B raw34636step0 raw34636step0Labels := by
      have ha : raw34636step0 = (fun i j => raw34636 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34636step0 raw34636; decide +kernel
      have hl : raw34636step0Labels = raw34636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34636 raw34636Labels permutation265 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw34637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34637step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34637 raw34637Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34637 raw34637Labels = mixedMoment B raw34637step0 raw34637step0Labels := by
      have ha : raw34637step0 = (fun i j => raw34637 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34637step0 raw34637; decide +kernel
      have hl : raw34637step0Labels = raw34637Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34637 raw34637Labels permutation240 permutation5
    mixedMoment B raw34637step0 raw34637step0Labels = mixedMoment B raw34637step1 raw34637step1Labels := by
      have ha : raw34637step1 = -raw34637step0 := by apply Matrix.ext; change ∀ i j, raw34637step1 i j = -(raw34637step0 i j); unfold raw34637step1 raw34637step0; decide +kernel
      have hl : raw34637step1Labels = raw34637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34637step1 raw34637step1Labels = mixedMoment B raw34637step2 raw34637step2Labels := by
      have ha : raw34637step2 = raw34637step1 := by apply Matrix.ext; unfold raw34637step2 raw34637step1; decide +kernel
      have hl : raw34637step1Labels = labelEmbedding8 ∘ raw34637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34637step1 raw34637step1Labels raw34637step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw34638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34638step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34638 raw34638Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34638 raw34638Labels = mixedMoment B raw34638step0 raw34638step0Labels := by
      have ha : raw34638step0 = (fun i j => raw34638 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34638step0 raw34638; decide +kernel
      have hl : raw34638step0Labels = raw34638Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34638 raw34638Labels permutation260 permutation5
    mixedMoment B raw34638step0 raw34638step0Labels = mixedMoment B raw34638step1 raw34638step1Labels := by
      have ha : raw34638step1 = -raw34638step0 := by apply Matrix.ext; change ∀ i j, raw34638step1 i j = -(raw34638step0 i j); unfold raw34638step1 raw34638step0; decide +kernel
      have hl : raw34638step1Labels = raw34638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34638step1 raw34638step1Labels = mixedMoment B raw34638step2 raw34638step2Labels := by
      have ha : raw34638step2 = raw34638step1 := by apply Matrix.ext; unfold raw34638step2 raw34638step1; decide +kernel
      have hl : raw34638step1Labels = labelEmbedding8 ∘ raw34638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34638step1 raw34638step1Labels raw34638step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw34639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34639step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34639 raw34639Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw34639 raw34639Labels = mixedMoment B raw34639step0 raw34639step0Labels := by
      have ha : raw34639step0 = (fun i j => raw34639 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34639step0 raw34639; decide +kernel
      have hl : raw34639step0Labels = raw34639Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34639 raw34639Labels permutation243 permutation5
    mixedMoment B raw34639step0 raw34639step0Labels = mixedMoment B raw34639step1 raw34639step1Labels := by
      have ha : raw34639step1 = -raw34639step0 := by apply Matrix.ext; change ∀ i j, raw34639step1 i j = -(raw34639step0 i j); unfold raw34639step1 raw34639step0; decide +kernel
      have hl : raw34639step1Labels = raw34639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34639step1 raw34639step1Labels = mixedMoment B raw34639step2 raw34639step2Labels := by
      have ha : raw34639step2 = raw34639step1 := by apply Matrix.ext; unfold raw34639step2 raw34639step1; decide +kernel
      have hl : raw34639step1Labels = labelEmbedding8 ∘ raw34639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34639step1 raw34639step1Labels raw34639step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw34640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34640step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34640 raw34640Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw34640 raw34640Labels = mixedMoment B raw34640step0 raw34640step0Labels := by
      have ha : raw34640step0 = (fun i j => raw34640 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34640step0 raw34640; decide +kernel
      have hl : raw34640step0Labels = raw34640Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34640 raw34640Labels permutation243 permutation5
    mixedMoment B raw34640step0 raw34640step0Labels = mixedMoment B raw34640step1 raw34640step1Labels := by
      have ha : raw34640step1 = -raw34640step0 := by apply Matrix.ext; change ∀ i j, raw34640step1 i j = -(raw34640step0 i j); unfold raw34640step1 raw34640step0; decide +kernel
      have hl : raw34640step1Labels = raw34640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34640step1 raw34640step1Labels = mixedMoment B raw34640step2 raw34640step2Labels := by
      have ha : raw34640step2 = raw34640step1 := by apply Matrix.ext; unfold raw34640step2 raw34640step1; decide +kernel
      have hl : raw34640step1Labels = labelEmbedding8 ∘ raw34640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34640step1 raw34640step1Labels raw34640step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw34641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34641step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34641step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34641 raw34641Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw34641 raw34641Labels = mixedMoment B raw34641step0 raw34641step0Labels := by
      have ha : raw34641step0 = (fun i j => raw34641 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34641step0 raw34641; decide +kernel
      have hl : raw34641step0Labels = raw34641Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34641 raw34641Labels permutation263 permutation5
    mixedMoment B raw34641step0 raw34641step0Labels = mixedMoment B raw34641step1 raw34641step1Labels := by
      have ha : raw34641step1 = -raw34641step0 := by apply Matrix.ext; change ∀ i j, raw34641step1 i j = -(raw34641step0 i j); unfold raw34641step1 raw34641step0; decide +kernel
      have hl : raw34641step1Labels = raw34641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34641step1 raw34641step1Labels = mixedMoment B raw34641step2 raw34641step2Labels := by
      have ha : raw34641step2 = raw34641step1 := by apply Matrix.ext; unfold raw34641step2 raw34641step1; decide +kernel
      have hl : raw34641step1Labels = labelEmbedding8 ∘ raw34641step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34641step1 raw34641step1Labels raw34641step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw34642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34642 raw34642Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw34642 raw34642Labels = mixedMoment B raw34642step0 raw34642step0Labels := by
      have ha : raw34642step0 = (fun i j => raw34642 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34642step0 raw34642; decide +kernel
      have hl : raw34642step0Labels = raw34642Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34642 raw34642Labels permutation169 permutation3
    mixedMoment B raw34642step0 raw34642step0Labels = mixedMoment B raw34642step1 raw34642step1Labels := by
      have ha : raw34642step1 = raw34642step0 := by apply Matrix.ext; unfold raw34642step1 raw34642step0; decide +kernel
      have hl : raw34642step0Labels = labelEmbedding6 ∘ raw34642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34642step0 raw34642step0Labels raw34642step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

def raw34643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34643 raw34643Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34643 raw34643Labels = mixedMoment B raw34643step0 raw34643step0Labels := by
      have ha : raw34643step0 = (fun i j => raw34643 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34643step0 raw34643; decide +kernel
      have hl : raw34643step0Labels = raw34643Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34643 raw34643Labels permutation169 permutation3
    mixedMoment B raw34643step0 raw34643step0Labels = mixedMoment B raw34643step1 raw34643step1Labels := by
      have ha : raw34643step1 = raw34643step0 := by apply Matrix.ext; unfold raw34643step1 raw34643step0; decide +kernel
      have hl : raw34643step0Labels = labelEmbedding6 ∘ raw34643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34643step0 raw34643step0Labels raw34643step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw34644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34644 raw34644Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw34644 raw34644Labels = mixedMoment B raw34644step0 raw34644step0Labels := by
      have hz : ∀ j, raw34644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34644step0 = (fun i j => raw34644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34644step0 raw34644; decide +kernel
      have hl : raw34644step0Labels = raw34644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34644 raw34644Labels permutation434 hz
    mixedMoment B raw34644step0 raw34644step0Labels = mixedMoment B raw34644step1 raw34644step1Labels := by
      have ha : raw34644step1 = (fun i j => raw34644step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34644step1 raw34644step0; decide +kernel
      have hl : raw34644step1Labels = raw34644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34644step0 raw34644step0Labels permutation35 permutation3
    mixedMoment B raw34644step1 raw34644step1Labels = mixedMoment B raw34644step2 raw34644step2Labels := by
      have ha : raw34644step2 = raw34644step1 := by apply Matrix.ext; unfold raw34644step2 raw34644step1; decide +kernel
      have hl : raw34644step1Labels = labelEmbedding6 ∘ raw34644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34644step1 raw34644step1Labels raw34644step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw34645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34645step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34645step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34645 raw34645Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34645 raw34645Labels = mixedMoment B raw34645step0 raw34645step0Labels := by
      have ha : raw34645step0 = (fun i j => raw34645 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34645step0 raw34645; decide +kernel
      have hl : raw34645step0Labels = raw34645Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34645 raw34645Labels permutation241 permutation5
    mixedMoment B raw34645step0 raw34645step0Labels = mixedMoment B raw34645step1 raw34645step1Labels := by
      have ha : raw34645step1 = -raw34645step0 := by apply Matrix.ext; change ∀ i j, raw34645step1 i j = -(raw34645step0 i j); unfold raw34645step1 raw34645step0; decide +kernel
      have hl : raw34645step1Labels = raw34645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34645step1 raw34645step1Labels = mixedMoment B raw34645step2 raw34645step2Labels := by
      have ha : raw34645step2 = raw34645step1 := by apply Matrix.ext; unfold raw34645step2 raw34645step1; decide +kernel
      have hl : raw34645step1Labels = labelEmbedding8 ∘ raw34645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34645step1 raw34645step1Labels raw34645step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34646step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34646 raw34646Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34646 raw34646Labels = mixedMoment B raw34646step0 raw34646step0Labels := by
      have ha : raw34646step0 = (fun i j => raw34646 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34646step0 raw34646; decide +kernel
      have hl : raw34646step0Labels = raw34646Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34646 raw34646Labels permutation261 permutation5
    mixedMoment B raw34646step0 raw34646step0Labels = mixedMoment B raw34646step1 raw34646step1Labels := by
      have ha : raw34646step1 = -raw34646step0 := by apply Matrix.ext; change ∀ i j, raw34646step1 i j = -(raw34646step0 i j); unfold raw34646step1 raw34646step0; decide +kernel
      have hl : raw34646step1Labels = raw34646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34646step1 raw34646step1Labels = mixedMoment B raw34646step2 raw34646step2Labels := by
      have ha : raw34646step2 = raw34646step1 := by apply Matrix.ext; unfold raw34646step2 raw34646step1; decide +kernel
      have hl : raw34646step1Labels = labelEmbedding8 ∘ raw34646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34646step1 raw34646step1Labels raw34646step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34647 raw34647Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw34647 raw34647Labels = mixedMoment B raw34647step0 raw34647step0Labels := by
      have ha : raw34647step0 = (fun i j => raw34647 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34647step0 raw34647; decide +kernel
      have hl : raw34647step0Labels = raw34647Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34647 raw34647Labels permutation168 permutation3
    mixedMoment B raw34647step0 raw34647step0Labels = mixedMoment B raw34647step1 raw34647step1Labels := by
      have ha : raw34647step1 = raw34647step0 := by apply Matrix.ext; unfold raw34647step1 raw34647step0; decide +kernel
      have hl : raw34647step0Labels = labelEmbedding6 ∘ raw34647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34647step0 raw34647step0Labels raw34647step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

def raw34648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34648step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34648 raw34648Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34648 raw34648Labels = mixedMoment B raw34648step0 raw34648step0Labels := by
      have ha : raw34648step0 = (fun i j => raw34648 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34648step0 raw34648; decide +kernel
      have hl : raw34648step0Labels = raw34648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34648 raw34648Labels permutation168 permutation3
    mixedMoment B raw34648step0 raw34648step0Labels = mixedMoment B raw34648step1 raw34648step1Labels := by
      have ha : raw34648step1 = raw34648step0 := by apply Matrix.ext; unfold raw34648step1 raw34648step0; decide +kernel
      have hl : raw34648step0Labels = labelEmbedding6 ∘ raw34648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34648step0 raw34648step0Labels raw34648step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw34649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34649 raw34649Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34649 raw34649Labels = mixedMoment B raw34649step0 raw34649step0Labels := by
      have ha : raw34649step0 = (fun i j => raw34649 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34649step0 raw34649; decide +kernel
      have hl : raw34649step0Labels = raw34649Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34649 raw34649Labels permutation240 permutation5
    mixedMoment B raw34649step0 raw34649step0Labels = mixedMoment B raw34649step1 raw34649step1Labels := by
      have ha : raw34649step1 = -raw34649step0 := by apply Matrix.ext; change ∀ i j, raw34649step1 i j = -(raw34649step0 i j); unfold raw34649step1 raw34649step0; decide +kernel
      have hl : raw34649step1Labels = raw34649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34649step1 raw34649step1Labels = mixedMoment B raw34649step2 raw34649step2Labels := by
      have ha : raw34649step2 = raw34649step1 := by apply Matrix.ext; unfold raw34649step2 raw34649step1; decide +kernel
      have hl : raw34649step1Labels = labelEmbedding8 ∘ raw34649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34649step1 raw34649step1Labels raw34649step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34650step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34650 raw34650Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34650 raw34650Labels = mixedMoment B raw34650step0 raw34650step0Labels := by
      have ha : raw34650step0 = (fun i j => raw34650 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34650step0 raw34650; decide +kernel
      have hl : raw34650step0Labels = raw34650Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34650 raw34650Labels permutation260 permutation5
    mixedMoment B raw34650step0 raw34650step0Labels = mixedMoment B raw34650step1 raw34650step1Labels := by
      have ha : raw34650step1 = -raw34650step0 := by apply Matrix.ext; change ∀ i j, raw34650step1 i j = -(raw34650step0 i j); unfold raw34650step1 raw34650step0; decide +kernel
      have hl : raw34650step1Labels = raw34650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34650step1 raw34650step1Labels = mixedMoment B raw34650step2 raw34650step2Labels := by
      have ha : raw34650step2 = raw34650step1 := by apply Matrix.ext; unfold raw34650step2 raw34650step1; decide +kernel
      have hl : raw34650step1Labels = labelEmbedding8 ∘ raw34650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34650step1 raw34650step1Labels raw34650step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34651 raw34651Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw34651 raw34651Labels = mixedMoment B raw34651step0 raw34651step0Labels := by
      have ha : raw34651step0 = (fun i j => raw34651 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34651step0 raw34651; decide +kernel
      have hl : raw34651step0Labels = raw34651Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34651 raw34651Labels permutation170 permutation3
    mixedMoment B raw34651step0 raw34651step0Labels = mixedMoment B raw34651step1 raw34651step1Labels := by
      have ha : raw34651step1 = raw34651step0 := by apply Matrix.ext; unfold raw34651step1 raw34651step0; decide +kernel
      have hl : raw34651step0Labels = labelEmbedding6 ∘ raw34651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34651step0 raw34651step0Labels raw34651step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw34652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34652 raw34652Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw34652 raw34652Labels = mixedMoment B raw34652step0 raw34652step0Labels := by
      have ha : raw34652step0 = (fun i j => raw34652 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34652step0 raw34652; decide +kernel
      have hl : raw34652step0Labels = raw34652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34652 raw34652Labels permutation170 permutation3
    mixedMoment B raw34652step0 raw34652step0Labels = mixedMoment B raw34652step1 raw34652step1Labels := by
      have ha : raw34652step1 = raw34652step0 := by apply Matrix.ext; unfold raw34652step1 raw34652step0; decide +kernel
      have hl : raw34652step0Labels = labelEmbedding6 ∘ raw34652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34652step0 raw34652step0Labels raw34652step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw34653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34653step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34653step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34653 raw34653Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34653 raw34653Labels = mixedMoment B raw34653step0 raw34653step0Labels := by
      have ha : raw34653step0 = (fun i j => raw34653 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34653step0 raw34653; decide +kernel
      have hl : raw34653step0Labels = raw34653Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34653 raw34653Labels permutation246 permutation5
    mixedMoment B raw34653step0 raw34653step0Labels = mixedMoment B raw34653step1 raw34653step1Labels := by
      have ha : raw34653step1 = -raw34653step0 := by apply Matrix.ext; change ∀ i j, raw34653step1 i j = -(raw34653step0 i j); unfold raw34653step1 raw34653step0; decide +kernel
      have hl : raw34653step1Labels = raw34653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34653step1 raw34653step1Labels = mixedMoment B raw34653step2 raw34653step2Labels := by
      have ha : raw34653step2 = raw34653step1 := by apply Matrix.ext; unfold raw34653step2 raw34653step1; decide +kernel
      have hl : raw34653step1Labels = labelEmbedding8 ∘ raw34653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34653step1 raw34653step1Labels raw34653step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34654 raw34654Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34654 raw34654Labels = mixedMoment B raw34654step0 raw34654step0Labels := by
      have ha : raw34654step0 = (fun i j => raw34654 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34654step0 raw34654; decide +kernel
      have hl : raw34654step0Labels = raw34654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34654 raw34654Labels permutation155 permutation6
    mixedMoment B raw34654step0 raw34654step0Labels = mixedMoment B raw34654step1 raw34654step1Labels := by
      have ha : raw34654step1 = raw34654step0 := by apply Matrix.ext; unfold raw34654step1 raw34654step0; decide +kernel
      have hl : raw34654step0Labels = labelEmbedding9 ∘ raw34654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34654step0 raw34654step0Labels raw34654step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34655 raw34655Labels = mixedMoment B node5202 node5202Labels := by
  calc
    mixedMoment B raw34655 raw34655Labels = mixedMoment B raw34655step0 raw34655step0Labels := by
      have ha : raw34655step0 = (fun i j => raw34655 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34655step0 raw34655; decide +kernel
      have hl : raw34655step0Labels = raw34655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34655 raw34655Labels permutation161 permutation6
    mixedMoment B raw34655step0 raw34655step0Labels = mixedMoment B raw34655step1 raw34655step1Labels := by
      have ha : raw34655step1 = raw34655step0 := by apply Matrix.ext; unfold raw34655step1 raw34655step0; decide +kernel
      have hl : raw34655step0Labels = labelEmbedding9 ∘ raw34655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34655step0 raw34655step0Labels raw34655step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5202 node5202Labels := by rfl

def raw34656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34656 raw34656Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34656 raw34656Labels = mixedMoment B raw34656step0 raw34656step0Labels := by
      have ha : raw34656step0 = (fun i j => raw34656 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34656step0 raw34656; decide +kernel
      have hl : raw34656step0Labels = raw34656Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34656 raw34656Labels permutation168 permutation6
    mixedMoment B raw34656step0 raw34656step0Labels = mixedMoment B raw34656step1 raw34656step1Labels := by
      have ha : raw34656step1 = raw34656step0 := by apply Matrix.ext; unfold raw34656step1 raw34656step0; decide +kernel
      have hl : raw34656step0Labels = labelEmbedding9 ∘ raw34656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34656step0 raw34656step0Labels raw34656step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw34657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34657step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34657step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34657step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34657 raw34657Labels = mixedMoment B node4441 node4441Labels := by
  calc
    mixedMoment B raw34657 raw34657Labels = mixedMoment B raw34657step0 raw34657step0Labels := by
      have ha : raw34657step0 = (fun i j => raw34657 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34657step0 raw34657; decide +kernel
      have hl : raw34657step0Labels = raw34657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34657 raw34657Labels permutation243 permutation4
    mixedMoment B raw34657step0 raw34657step0Labels = mixedMoment B raw34657step1 raw34657step1Labels := by
      have ha : raw34657step1 = -raw34657step0 := by apply Matrix.ext; change ∀ i j, raw34657step1 i j = -(raw34657step0 i j); unfold raw34657step1 raw34657step0; decide +kernel
      have hl : raw34657step1Labels = raw34657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34657step1 raw34657step1Labels = mixedMoment B raw34657step2 raw34657step2Labels := by
      have ha : raw34657step2 = raw34657step1 := by apply Matrix.ext; unfold raw34657step2 raw34657step1; decide +kernel
      have hl : raw34657step1Labels = labelEmbedding7 ∘ raw34657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34657step1 raw34657step1Labels raw34657step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4441 node4441Labels := by rfl

def raw34658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34658 raw34658Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw34658 raw34658Labels = mixedMoment B raw34658step0 raw34658step0Labels := by
      have ha : raw34658step0 = (fun i j => raw34658 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34658step0 raw34658; decide +kernel
      have hl : raw34658step0Labels = raw34658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34658 raw34658Labels permutation155 permutation6
    mixedMoment B raw34658step0 raw34658step0Labels = mixedMoment B raw34658step1 raw34658step1Labels := by
      have ha : raw34658step1 = raw34658step0 := by apply Matrix.ext; unfold raw34658step1 raw34658step0; decide +kernel
      have hl : raw34658step0Labels = labelEmbedding9 ∘ raw34658step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34658step0 raw34658step0Labels raw34658step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw34659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34659 raw34659Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw34659 raw34659Labels = mixedMoment B raw34659step0 raw34659step0Labels := by
      have ha : raw34659step0 = (fun i j => raw34659 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34659step0 raw34659; decide +kernel
      have hl : raw34659step0Labels = raw34659Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34659 raw34659Labels permutation161 permutation6
    mixedMoment B raw34659step0 raw34659step0Labels = mixedMoment B raw34659step1 raw34659step1Labels := by
      have ha : raw34659step1 = raw34659step0 := by apply Matrix.ext; unfold raw34659step1 raw34659step0; decide +kernel
      have hl : raw34659step0Labels = labelEmbedding9 ∘ raw34659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34659step0 raw34659step0Labels raw34659step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw34660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34660step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34660 raw34660Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw34660 raw34660Labels = mixedMoment B raw34660step0 raw34660step0Labels := by
      have ha : raw34660step0 = (fun i j => raw34660 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34660step0 raw34660; decide +kernel
      have hl : raw34660step0Labels = raw34660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34660 raw34660Labels permutation243 permutation4
    mixedMoment B raw34660step0 raw34660step0Labels = mixedMoment B raw34660step1 raw34660step1Labels := by
      have ha : raw34660step1 = -raw34660step0 := by apply Matrix.ext; change ∀ i j, raw34660step1 i j = -(raw34660step0 i j); unfold raw34660step1 raw34660step0; decide +kernel
      have hl : raw34660step1Labels = raw34660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34660step1 raw34660step1Labels = mixedMoment B raw34660step2 raw34660step2Labels := by
      have ha : raw34660step2 = raw34660step1 := by apply Matrix.ext; unfold raw34660step2 raw34660step1; decide +kernel
      have hl : raw34660step1Labels = labelEmbedding7 ∘ raw34660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34660step1 raw34660step1Labels raw34660step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

def raw34661 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw34661step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34661step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34661 raw34661Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw34661 raw34661Labels = mixedMoment B raw34661step0 raw34661step0Labels := by
      have ha : raw34661step0 = (fun i j => raw34661 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34661step0 raw34661; decide +kernel
      have hl : raw34661step0Labels = raw34661Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34661 raw34661Labels permutation263 permutation4
    mixedMoment B raw34661step0 raw34661step0Labels = mixedMoment B raw34661step1 raw34661step1Labels := by
      have ha : raw34661step1 = -raw34661step0 := by apply Matrix.ext; change ∀ i j, raw34661step1 i j = -(raw34661step0 i j); unfold raw34661step1 raw34661step0; decide +kernel
      have hl : raw34661step1Labels = raw34661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34661step1 raw34661step1Labels = mixedMoment B raw34661step2 raw34661step2Labels := by
      have ha : raw34661step2 = raw34661step1 := by apply Matrix.ext; unfold raw34661step2 raw34661step1; decide +kernel
      have hl : raw34661step1Labels = labelEmbedding7 ∘ raw34661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34661step1 raw34661step1Labels raw34661step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

def raw34662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34662 raw34662Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw34662 raw34662Labels = mixedMoment B raw34662step0 raw34662step0Labels := by
      have ha : raw34662step0 = (fun i j => raw34662 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34662step0 raw34662; decide +kernel
      have hl : raw34662step0Labels = raw34662Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34662 raw34662Labels permutation241 permutation4
    mixedMoment B raw34662step0 raw34662step0Labels = mixedMoment B raw34662step1 raw34662step1Labels := by
      have ha : raw34662step1 = -raw34662step0 := by apply Matrix.ext; change ∀ i j, raw34662step1 i j = -(raw34662step0 i j); unfold raw34662step1 raw34662step0; decide +kernel
      have hl : raw34662step1Labels = raw34662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34662step1 raw34662step1Labels = mixedMoment B raw34662step2 raw34662step2Labels := by
      have ha : raw34662step2 = raw34662step1 := by apply Matrix.ext; unfold raw34662step2 raw34662step1; decide +kernel
      have hl : raw34662step1Labels = labelEmbedding7 ∘ raw34662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34662step1 raw34662step1Labels raw34662step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

def raw34663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34663 raw34663Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34663 raw34663Labels = mixedMoment B raw34663step0 raw34663step0Labels := by
      have ha : raw34663step0 = (fun i j => raw34663 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34663step0 raw34663; decide +kernel
      have hl : raw34663step0Labels = raw34663Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34663 raw34663Labels permutation169 permutation6
    mixedMoment B raw34663step0 raw34663step0Labels = mixedMoment B raw34663step1 raw34663step1Labels := by
      have ha : raw34663step1 = raw34663step0 := by apply Matrix.ext; unfold raw34663step1 raw34663step0; decide +kernel
      have hl : raw34663step0Labels = labelEmbedding9 ∘ raw34663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34663step0 raw34663step0Labels raw34663step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34664 raw34664Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw34664 raw34664Labels = mixedMoment B raw34664step0 raw34664step0Labels := by
      have ha : raw34664step0 = (fun i j => raw34664 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34664step0 raw34664; decide +kernel
      have hl : raw34664step0Labels = raw34664Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34664 raw34664Labels permutation161 permutation6
    mixedMoment B raw34664step0 raw34664step0Labels = mixedMoment B raw34664step1 raw34664step1Labels := by
      have ha : raw34664step1 = raw34664step0 := by apply Matrix.ext; unfold raw34664step1 raw34664step0; decide +kernel
      have hl : raw34664step0Labels = labelEmbedding9 ∘ raw34664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34664step0 raw34664step0Labels raw34664step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw34665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34665step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34665 raw34665Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34665 raw34665Labels = mixedMoment B raw34665step0 raw34665step0Labels := by
      have ha : raw34665step0 = (fun i j => raw34665 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34665step0 raw34665; decide +kernel
      have hl : raw34665step0Labels = raw34665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34665 raw34665Labels permutation241 permutation4
    mixedMoment B raw34665step0 raw34665step0Labels = mixedMoment B raw34665step1 raw34665step1Labels := by
      have ha : raw34665step1 = -raw34665step0 := by apply Matrix.ext; change ∀ i j, raw34665step1 i j = -(raw34665step0 i j); unfold raw34665step1 raw34665step0; decide +kernel
      have hl : raw34665step1Labels = raw34665step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34665step1 raw34665step1Labels = mixedMoment B raw34665step2 raw34665step2Labels := by
      have ha : raw34665step2 = raw34665step1 := by apply Matrix.ext; unfold raw34665step2 raw34665step1; decide +kernel
      have hl : raw34665step1Labels = labelEmbedding7 ∘ raw34665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34665step1 raw34665step1Labels raw34665step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw34666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34666step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34666step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34666 raw34666Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34666 raw34666Labels = mixedMoment B raw34666step0 raw34666step0Labels := by
      have ha : raw34666step0 = (fun i j => raw34666 (permutation261 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34666step0 raw34666; decide +kernel
      have hl : raw34666step0Labels = raw34666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34666 raw34666Labels permutation261 permutation4
    mixedMoment B raw34666step0 raw34666step0Labels = mixedMoment B raw34666step1 raw34666step1Labels := by
      have ha : raw34666step1 = -raw34666step0 := by apply Matrix.ext; change ∀ i j, raw34666step1 i j = -(raw34666step0 i j); unfold raw34666step1 raw34666step0; decide +kernel
      have hl : raw34666step1Labels = raw34666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34666step1 raw34666step1Labels = mixedMoment B raw34666step2 raw34666step2Labels := by
      have ha : raw34666step2 = raw34666step1 := by apply Matrix.ext; unfold raw34666step2 raw34666step1; decide +kernel
      have hl : raw34666step1Labels = labelEmbedding7 ∘ raw34666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34666step1 raw34666step1Labels raw34666step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw34667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34667step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34667 raw34667Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw34667 raw34667Labels = mixedMoment B raw34667step0 raw34667step0Labels := by
      have ha : raw34667step0 = (fun i j => raw34667 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34667step0 raw34667; decide +kernel
      have hl : raw34667step0Labels = raw34667Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34667 raw34667Labels permutation240 permutation4
    mixedMoment B raw34667step0 raw34667step0Labels = mixedMoment B raw34667step1 raw34667step1Labels := by
      have ha : raw34667step1 = -raw34667step0 := by apply Matrix.ext; change ∀ i j, raw34667step1 i j = -(raw34667step0 i j); unfold raw34667step1 raw34667step0; decide +kernel
      have hl : raw34667step1Labels = raw34667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34667step1 raw34667step1Labels = mixedMoment B raw34667step2 raw34667step2Labels := by
      have ha : raw34667step2 = raw34667step1 := by apply Matrix.ext; unfold raw34667step2 raw34667step1; decide +kernel
      have hl : raw34667step1Labels = labelEmbedding7 ∘ raw34667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34667step1 raw34667step1Labels raw34667step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

def raw34668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34668 raw34668Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34668 raw34668Labels = mixedMoment B raw34668step0 raw34668step0Labels := by
      have ha : raw34668step0 = (fun i j => raw34668 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34668step0 raw34668; decide +kernel
      have hl : raw34668step0Labels = raw34668Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34668 raw34668Labels permutation168 permutation6
    mixedMoment B raw34668step0 raw34668step0Labels = mixedMoment B raw34668step1 raw34668step1Labels := by
      have ha : raw34668step1 = raw34668step0 := by apply Matrix.ext; unfold raw34668step1 raw34668step0; decide +kernel
      have hl : raw34668step0Labels = labelEmbedding9 ∘ raw34668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34668step0 raw34668step0Labels raw34668step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34669 raw34669Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw34669 raw34669Labels = mixedMoment B raw34669step0 raw34669step0Labels := by
      have ha : raw34669step0 = (fun i j => raw34669 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34669step0 raw34669; decide +kernel
      have hl : raw34669step0Labels = raw34669Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34669 raw34669Labels permutation155 permutation6
    mixedMoment B raw34669step0 raw34669step0Labels = mixedMoment B raw34669step1 raw34669step1Labels := by
      have ha : raw34669step1 = raw34669step0 := by apply Matrix.ext; unfold raw34669step1 raw34669step0; decide +kernel
      have hl : raw34669step0Labels = labelEmbedding9 ∘ raw34669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34669step0 raw34669step0Labels raw34669step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw34670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw34670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34670step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34670step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34670 raw34670Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34670 raw34670Labels = mixedMoment B raw34670step0 raw34670step0Labels := by
      have ha : raw34670step0 = (fun i j => raw34670 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34670step0 raw34670; decide +kernel
      have hl : raw34670step0Labels = raw34670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34670 raw34670Labels permutation240 permutation4
    mixedMoment B raw34670step0 raw34670step0Labels = mixedMoment B raw34670step1 raw34670step1Labels := by
      have ha : raw34670step1 = -raw34670step0 := by apply Matrix.ext; change ∀ i j, raw34670step1 i j = -(raw34670step0 i j); unfold raw34670step1 raw34670step0; decide +kernel
      have hl : raw34670step1Labels = raw34670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34670step1 raw34670step1Labels = mixedMoment B raw34670step2 raw34670step2Labels := by
      have ha : raw34670step2 = raw34670step1 := by apply Matrix.ext; unfold raw34670step2 raw34670step1; decide +kernel
      have hl : raw34670step1Labels = labelEmbedding7 ∘ raw34670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34670step1 raw34670step1Labels raw34670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw34671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34671step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34671 raw34671Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw34671 raw34671Labels = mixedMoment B raw34671step0 raw34671step0Labels := by
      have ha : raw34671step0 = (fun i j => raw34671 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34671step0 raw34671; decide +kernel
      have hl : raw34671step0Labels = raw34671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34671 raw34671Labels permutation260 permutation4
    mixedMoment B raw34671step0 raw34671step0Labels = mixedMoment B raw34671step1 raw34671step1Labels := by
      have ha : raw34671step1 = -raw34671step0 := by apply Matrix.ext; change ∀ i j, raw34671step1 i j = -(raw34671step0 i j); unfold raw34671step1 raw34671step0; decide +kernel
      have hl : raw34671step1Labels = raw34671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34671step1 raw34671step1Labels = mixedMoment B raw34671step2 raw34671step2Labels := by
      have ha : raw34671step2 = raw34671step1 := by apply Matrix.ext; unfold raw34671step2 raw34671step1; decide +kernel
      have hl : raw34671step1Labels = labelEmbedding7 ∘ raw34671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34671step1 raw34671step1Labels raw34671step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw34672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34672 raw34672Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw34672 raw34672Labels = mixedMoment B raw34672step0 raw34672step0Labels := by
      have ha : raw34672step0 = (fun i j => raw34672 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34672step0 raw34672; decide +kernel
      have hl : raw34672step0Labels = raw34672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34672 raw34672Labels permutation246 permutation4
    mixedMoment B raw34672step0 raw34672step0Labels = mixedMoment B raw34672step1 raw34672step1Labels := by
      have ha : raw34672step1 = -raw34672step0 := by apply Matrix.ext; change ∀ i j, raw34672step1 i j = -(raw34672step0 i j); unfold raw34672step1 raw34672step0; decide +kernel
      have hl : raw34672step1Labels = raw34672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34672step1 raw34672step1Labels = mixedMoment B raw34672step2 raw34672step2Labels := by
      have ha : raw34672step2 = raw34672step1 := by apply Matrix.ext; unfold raw34672step2 raw34672step1; decide +kernel
      have hl : raw34672step1Labels = labelEmbedding7 ∘ raw34672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34672step1 raw34672step1Labels raw34672step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw34673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34673 raw34673Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34673 raw34673Labels = mixedMoment B raw34673step0 raw34673step0Labels := by
      have ha : raw34673step0 = (fun i j => raw34673 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34673step0 raw34673; decide +kernel
      have hl : raw34673step0Labels = raw34673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34673 raw34673Labels permutation156 permutation6
    mixedMoment B raw34673step0 raw34673step0Labels = mixedMoment B raw34673step1 raw34673step1Labels := by
      have ha : raw34673step1 = raw34673step0 := by apply Matrix.ext; unfold raw34673step1 raw34673step0; decide +kernel
      have hl : raw34673step0Labels = labelEmbedding9 ∘ raw34673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34673step0 raw34673step0Labels raw34673step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw34674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34674 raw34674Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34674 raw34674Labels = mixedMoment B raw34674step0 raw34674step0Labels := by
      have ha : raw34674step0 = (fun i j => raw34674 (permutation162 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34674step0 raw34674; decide +kernel
      have hl : raw34674step0Labels = raw34674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34674 raw34674Labels permutation162 permutation6
    mixedMoment B raw34674step0 raw34674step0Labels = mixedMoment B raw34674step1 raw34674step1Labels := by
      have ha : raw34674step1 = raw34674step0 := by apply Matrix.ext; unfold raw34674step1 raw34674step0; decide +kernel
      have hl : raw34674step0Labels = labelEmbedding9 ∘ raw34674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34674step0 raw34674step0Labels raw34674step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw34675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34675 raw34675Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw34675 raw34675Labels = mixedMoment B raw34675step0 raw34675step0Labels := by
      have ha : raw34675step0 = (fun i j => raw34675 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34675step0 raw34675; decide +kernel
      have hl : raw34675step0Labels = raw34675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34675 raw34675Labels permutation224 permutation4
    mixedMoment B raw34675step0 raw34675step0Labels = mixedMoment B raw34675step1 raw34675step1Labels := by
      have ha : raw34675step1 = -raw34675step0 := by apply Matrix.ext; change ∀ i j, raw34675step1 i j = -(raw34675step0 i j); unfold raw34675step1 raw34675step0; decide +kernel
      have hl : raw34675step1Labels = raw34675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34675step1 raw34675step1Labels = mixedMoment B raw34675step2 raw34675step2Labels := by
      have ha : raw34675step2 = raw34675step1 := by apply Matrix.ext; unfold raw34675step2 raw34675step1; decide +kernel
      have hl : raw34675step1Labels = labelEmbedding7 ∘ raw34675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34675step1 raw34675step1Labels raw34675step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw34676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34676 raw34676Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw34676 raw34676Labels = mixedMoment B raw34676step0 raw34676step0Labels := by
      have ha : raw34676step0 = (fun i j => raw34676 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34676step0 raw34676; decide +kernel
      have hl : raw34676step0Labels = raw34676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34676 raw34676Labels permutation164 permutation6
    mixedMoment B raw34676step0 raw34676step0Labels = mixedMoment B raw34676step1 raw34676step1Labels := by
      have ha : raw34676step1 = raw34676step0 := by apply Matrix.ext; unfold raw34676step1 raw34676step0; decide +kernel
      have hl : raw34676step0Labels = labelEmbedding9 ∘ raw34676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34676step0 raw34676step0Labels raw34676step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw34677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34677 raw34677Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34677 raw34677Labels = mixedMoment B raw34677step0 raw34677step0Labels := by
      have ha : raw34677step0 = (fun i j => raw34677 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34677step0 raw34677; decide +kernel
      have hl : raw34677step0Labels = raw34677Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34677 raw34677Labels permutation154 permutation6
    mixedMoment B raw34677step0 raw34677step0Labels = mixedMoment B raw34677step1 raw34677step1Labels := by
      have ha : raw34677step1 = raw34677step0 := by apply Matrix.ext; unfold raw34677step1 raw34677step0; decide +kernel
      have hl : raw34677step0Labels = labelEmbedding9 ∘ raw34677step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34677step0 raw34677step0Labels raw34677step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw34678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw34678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34678 raw34678Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw34678 raw34678Labels = mixedMoment B raw34678step0 raw34678step0Labels := by
      have ha : raw34678step0 = (fun i j => raw34678 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34678step0 raw34678; decide +kernel
      have hl : raw34678step0Labels = raw34678Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34678 raw34678Labels permutation160 permutation6
    mixedMoment B raw34678step0 raw34678step0Labels = mixedMoment B raw34678step1 raw34678step1Labels := by
      have ha : raw34678step1 = raw34678step0 := by apply Matrix.ext; unfold raw34678step1 raw34678step0; decide +kernel
      have hl : raw34678step0Labels = labelEmbedding9 ∘ raw34678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34678step0 raw34678step0Labels raw34678step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw34679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw34679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34679step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34679step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34679 raw34679Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw34679 raw34679Labels = mixedMoment B raw34679step0 raw34679step0Labels := by
      have ha : raw34679step0 = (fun i j => raw34679 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34679step0 raw34679; decide +kernel
      have hl : raw34679step0Labels = raw34679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34679 raw34679Labels permutation224 permutation4
    mixedMoment B raw34679step0 raw34679step0Labels = mixedMoment B raw34679step1 raw34679step1Labels := by
      have ha : raw34679step1 = -raw34679step0 := by apply Matrix.ext; change ∀ i j, raw34679step1 i j = -(raw34679step0 i j); unfold raw34679step1 raw34679step0; decide +kernel
      have hl : raw34679step1Labels = raw34679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34679step1 raw34679step1Labels = mixedMoment B raw34679step2 raw34679step2Labels := by
      have ha : raw34679step2 = raw34679step1 := by apply Matrix.ext; unfold raw34679step2 raw34679step1; decide +kernel
      have hl : raw34679step1Labels = labelEmbedding7 ∘ raw34679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34679step1 raw34679step1Labels raw34679step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

def raw34680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34680step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34680step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34680 raw34680Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw34680 raw34680Labels = mixedMoment B raw34680step0 raw34680step0Labels := by
      have ha : raw34680step0 = (fun i j => raw34680 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34680step0 raw34680; decide +kernel
      have hl : raw34680step0Labels = raw34680Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34680 raw34680Labels permutation169 permutation7
    mixedMoment B raw34680step0 raw34680step0Labels = mixedMoment B raw34680step1 raw34680step1Labels := by
      have ha : raw34680step1 = -raw34680step0 := by apply Matrix.ext; change ∀ i j, raw34680step1 i j = -(raw34680step0 i j); unfold raw34680step1 raw34680step0; decide +kernel
      have hl : raw34680step1Labels = raw34680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34680step1 raw34680step1Labels = mixedMoment B raw34680step2 raw34680step2Labels := by
      have ha : raw34680step2 = raw34680step1 := by apply Matrix.ext; unfold raw34680step2 raw34680step1; decide +kernel
      have hl : raw34680step1Labels = labelEmbedding10 ∘ raw34680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34680step1 raw34680step1Labels raw34680step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw34681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34681step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34681step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34681 raw34681Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw34681 raw34681Labels = mixedMoment B raw34681step0 raw34681step0Labels := by
      have ha : raw34681step0 = (fun i j => raw34681 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34681step0 raw34681; decide +kernel
      have hl : raw34681step0Labels = raw34681Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34681 raw34681Labels permutation169 permutation7
    mixedMoment B raw34681step0 raw34681step0Labels = mixedMoment B raw34681step1 raw34681step1Labels := by
      have ha : raw34681step1 = -raw34681step0 := by apply Matrix.ext; change ∀ i j, raw34681step1 i j = -(raw34681step0 i j); unfold raw34681step1 raw34681step0; decide +kernel
      have hl : raw34681step1Labels = raw34681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34681step1 raw34681step1Labels = mixedMoment B raw34681step2 raw34681step2Labels := by
      have ha : raw34681step2 = raw34681step1 := by apply Matrix.ext; unfold raw34681step2 raw34681step1; decide +kernel
      have hl : raw34681step1Labels = labelEmbedding10 ∘ raw34681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34681step1 raw34681step1Labels raw34681step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw34682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34682step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34682 raw34682Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw34682 raw34682Labels = mixedMoment B raw34682step0 raw34682step0Labels := by
      have ha : raw34682step0 = (fun i j => raw34682 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34682step0 raw34682; decide +kernel
      have hl : raw34682step0Labels = raw34682Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34682 raw34682Labels permutation169 permutation7
    mixedMoment B raw34682step0 raw34682step0Labels = mixedMoment B raw34682step1 raw34682step1Labels := by
      have ha : raw34682step1 = -raw34682step0 := by apply Matrix.ext; change ∀ i j, raw34682step1 i j = -(raw34682step0 i j); unfold raw34682step1 raw34682step0; decide +kernel
      have hl : raw34682step1Labels = raw34682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34682step1 raw34682step1Labels = mixedMoment B raw34682step2 raw34682step2Labels := by
      have ha : raw34682step2 = raw34682step1 := by apply Matrix.ext; unfold raw34682step2 raw34682step1; decide +kernel
      have hl : raw34682step1Labels = labelEmbedding10 ∘ raw34682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34682step1 raw34682step1Labels raw34682step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw34683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34683step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34683step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34683 raw34683Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34683 raw34683Labels = mixedMoment B raw34683step0 raw34683step0Labels := by
      have hz : ∀ j, raw34683 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34683step0 = (fun i j => raw34683 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34683step0 raw34683; decide +kernel
      have hl : raw34683step0Labels = raw34683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34683 raw34683Labels permutation520 hz
    mixedMoment B raw34683step0 raw34683step0Labels = mixedMoment B raw34683step1 raw34683step1Labels := by
      have ha : raw34683step1 = (fun i j => raw34683step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34683step1 raw34683step0; decide +kernel
      have hl : raw34683step1Labels = raw34683step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34683step0 raw34683step0Labels permutation37 permutation7
    mixedMoment B raw34683step1 raw34683step1Labels = mixedMoment B raw34683step2 raw34683step2Labels := by
      have ha : raw34683step2 = -raw34683step1 := by apply Matrix.ext; change ∀ i j, raw34683step2 i j = -(raw34683step1 i j); unfold raw34683step2 raw34683step1; decide +kernel
      have hl : raw34683step2Labels = raw34683step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34683step2 raw34683step2Labels = mixedMoment B raw34683step3 raw34683step3Labels := by
      have ha : raw34683step3 = raw34683step2 := by apply Matrix.ext; unfold raw34683step3 raw34683step2; decide +kernel
      have hl : raw34683step2Labels = labelEmbedding10 ∘ raw34683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34683step2 raw34683step2Labels raw34683step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw34684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34684step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34684step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34684step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34684 raw34684Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34684 raw34684Labels = mixedMoment B raw34684step0 raw34684step0Labels := by
      have hz : ∀ j, raw34684 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34684step0 = (fun i j => raw34684 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34684step0 raw34684; decide +kernel
      have hl : raw34684step0Labels = raw34684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34684 raw34684Labels permutation590 hz
    mixedMoment B raw34684step0 raw34684step0Labels = mixedMoment B raw34684step1 raw34684step1Labels := by
      have ha : raw34684step1 = (fun i j => raw34684step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34684step1 raw34684step0; decide +kernel
      have hl : raw34684step1Labels = raw34684step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34684step0 raw34684step0Labels permutation37 permutation7
    mixedMoment B raw34684step1 raw34684step1Labels = mixedMoment B raw34684step2 raw34684step2Labels := by
      have ha : raw34684step2 = -raw34684step1 := by apply Matrix.ext; change ∀ i j, raw34684step2 i j = -(raw34684step1 i j); unfold raw34684step2 raw34684step1; decide +kernel
      have hl : raw34684step2Labels = raw34684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34684step2 raw34684step2Labels = mixedMoment B raw34684step3 raw34684step3Labels := by
      have ha : raw34684step3 = raw34684step2 := by apply Matrix.ext; unfold raw34684step3 raw34684step2; decide +kernel
      have hl : raw34684step2Labels = labelEmbedding10 ∘ raw34684step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34684step2 raw34684step2Labels raw34684step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw34685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34685 raw34685Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw34685 raw34685Labels = mixedMoment B raw34685step0 raw34685step0Labels := by
      have hz : ∀ j, raw34685 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34685step0 = (fun i j => raw34685 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34685step0 raw34685; decide +kernel
      have hl : raw34685step0Labels = raw34685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34685 raw34685Labels permutation265 hz
    mixedMoment B raw34685step0 raw34685step0Labels = mixedMoment B raw34685step1 raw34685step1Labels := by
      have ha : raw34685step1 = (fun i j => raw34685step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34685step1 raw34685step0; decide +kernel
      have hl : raw34685step1Labels = raw34685step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34685step0 raw34685step0Labels permutation49 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw34686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34686 raw34686Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw34686 raw34686Labels = mixedMoment B raw34686step0 raw34686step0Labels := by
      have ha : raw34686step0 = (fun i j => raw34686 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34686step0 raw34686; decide +kernel
      have hl : raw34686step0Labels = raw34686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34686 raw34686Labels permutation169 permutation2
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw34687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34687 raw34687Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34687 raw34687Labels = mixedMoment B raw34687step0 raw34687step0Labels := by
      have ha : raw34687step0 = (fun i j => raw34687 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34687step0 raw34687; decide +kernel
      have hl : raw34687step0Labels = raw34687Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34687 raw34687Labels permutation161 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
