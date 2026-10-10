import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw36480Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36480 raw36480Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36480 raw36480Labels = mixedMoment B raw36480step0 raw36480step0Labels := by
      have ha : raw36480step0 = (fun i j => raw36480 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36480step0 raw36480; decide +kernel
      have hl : raw36480step0Labels = raw36480Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36480 raw36480Labels permutation277 permutation7
    mixedMoment B raw36480step0 raw36480step0Labels = mixedMoment B raw36480step1 raw36480step1Labels := by
      have ha : raw36480step1 = -raw36480step0 := by apply Matrix.ext; change ∀ i j, raw36480step1 i j = -(raw36480step0 i j); unfold raw36480step1 raw36480step0; decide +kernel
      have hl : raw36480step1Labels = raw36480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36480step1 raw36480step1Labels = mixedMoment B raw36480step2 raw36480step2Labels := by
      have ha : raw36480step2 = raw36480step1 := by apply Matrix.ext; unfold raw36480step2 raw36480step1; decide +kernel
      have hl : raw36480step1Labels = labelEmbedding1 ∘ raw36480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36480step1 raw36480step1Labels raw36480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw36481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36481Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36481 raw36481Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw36481 raw36481Labels = mixedMoment B raw36481step0 raw36481step0Labels := by
      have ha : raw36481step0 = (fun i j => raw36481 (permutation686 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36481step0 raw36481; decide +kernel
      have hl : raw36481step0Labels = raw36481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36481 raw36481Labels permutation686 permutation5
    mixedMoment B raw36481step0 raw36481step0Labels = mixedMoment B raw36481step1 raw36481step1Labels := by
      have ha : raw36481step1 = raw36481step0 := by apply Matrix.ext; unfold raw36481step1 raw36481step0; decide +kernel
      have hl : raw36481step0Labels = labelEmbedding1 ∘ raw36481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36481step0 raw36481step0Labels raw36481step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw36482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36482Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36482step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36482 raw36482Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw36482 raw36482Labels = mixedMoment B raw36482step0 raw36482step0Labels := by
      have ha : raw36482step0 = (fun i j => raw36482 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36482step0 raw36482; decide +kernel
      have hl : raw36482step0Labels = raw36482Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36482 raw36482Labels permutation277 permutation7
    mixedMoment B raw36482step0 raw36482step0Labels = mixedMoment B raw36482step1 raw36482step1Labels := by
      have ha : raw36482step1 = -raw36482step0 := by apply Matrix.ext; change ∀ i j, raw36482step1 i j = -(raw36482step0 i j); unfold raw36482step1 raw36482step0; decide +kernel
      have hl : raw36482step1Labels = raw36482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36482step1 raw36482step1Labels = mixedMoment B raw36482step2 raw36482step2Labels := by
      have ha : raw36482step2 = raw36482step1 := by apply Matrix.ext; unfold raw36482step2 raw36482step1; decide +kernel
      have hl : raw36482step1Labels = labelEmbedding1 ∘ raw36482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36482step1 raw36482step1Labels raw36482step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw36483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36483Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36483 raw36483Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw36483 raw36483Labels = mixedMoment B raw36483step0 raw36483step0Labels := by
      have ha : raw36483step0 = (fun i j => raw36483 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36483step0 raw36483; decide +kernel
      have hl : raw36483step0Labels = raw36483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36483 raw36483Labels permutation685 permutation5
    mixedMoment B raw36483step0 raw36483step0Labels = mixedMoment B raw36483step1 raw36483step1Labels := by
      have ha : raw36483step1 = raw36483step0 := by apply Matrix.ext; unfold raw36483step1 raw36483step0; decide +kernel
      have hl : raw36483step0Labels = labelEmbedding1 ∘ raw36483step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36483step0 raw36483step0Labels raw36483step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

def raw36484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw36484Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36484step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw36484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw36484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36484 raw36484Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw36484 raw36484Labels = mixedMoment B raw36484step0 raw36484step0Labels := by
      have hz : ∀ j, raw36484 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36484step0 = (fun i j => raw36484 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36484step0 raw36484; decide +kernel
      have hl : raw36484step0Labels = raw36484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36484 raw36484Labels permutation520 hz
    mixedMoment B raw36484step0 raw36484step0Labels = mixedMoment B raw36484step1 raw36484step1Labels := by
      have ha : raw36484step1 = (fun i j => raw36484step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36484step1 raw36484step0; decide +kernel
      have hl : raw36484step1Labels = raw36484step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36484step0 raw36484step0Labels permutation149 permutation5
    mixedMoment B raw36484step1 raw36484step1Labels = mixedMoment B raw36484step2 raw36484step2Labels := by
      have ha : raw36484step2 = raw36484step1 := by apply Matrix.ext; unfold raw36484step2 raw36484step1; decide +kernel
      have hl : raw36484step1Labels = labelEmbedding1 ∘ raw36484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36484step1 raw36484step1Labels raw36484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw36485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36485step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36485 raw36485Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw36485 raw36485Labels = mixedMoment B raw36485step0 raw36485step0Labels := by
      have ha : raw36485step0 = (fun i j => raw36485 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36485step0 raw36485; decide +kernel
      have hl : raw36485step0Labels = raw36485Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36485 raw36485Labels permutation267 permutation3
    mixedMoment B raw36485step0 raw36485step0Labels = mixedMoment B raw36485step1 raw36485step1Labels := by
      have ha : raw36485step1 = raw36485step0 := by apply Matrix.ext; unfold raw36485step1 raw36485step0; decide +kernel
      have hl : raw36485step0Labels = labelEmbedding6 ∘ raw36485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36485step0 raw36485step0Labels raw36485step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw36486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36486 raw36486Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw36486 raw36486Labels = mixedMoment B raw36486step0 raw36486step0Labels := by
      have ha : raw36486step0 = (fun i j => raw36486 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36486step0 raw36486; decide +kernel
      have hl : raw36486step0Labels = raw36486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36486 raw36486Labels permutation267 permutation3
    mixedMoment B raw36486step0 raw36486step0Labels = mixedMoment B raw36486step1 raw36486step1Labels := by
      have ha : raw36486step1 = raw36486step0 := by apply Matrix.ext; unfold raw36486step1 raw36486step0; decide +kernel
      have hl : raw36486step0Labels = labelEmbedding6 ∘ raw36486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36486step0 raw36486step0Labels raw36486step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw36487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36487 raw36487Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36487 raw36487Labels = mixedMoment B raw36487step0 raw36487step0Labels := by
      have hz : ∀ j, raw36487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36487step0 = (fun i j => raw36487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36487step0 raw36487; decide +kernel
      have hl : raw36487step0Labels = raw36487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36487 raw36487Labels permutation434 hz
    mixedMoment B raw36487step0 raw36487step0Labels = mixedMoment B raw36487step1 raw36487step1Labels := by
      have ha : raw36487step1 = (fun i j => raw36487step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36487step1 raw36487step0; decide +kernel
      have hl : raw36487step1Labels = raw36487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36487step0 raw36487step0Labels permutation56 permutation3
    mixedMoment B raw36487step1 raw36487step1Labels = mixedMoment B raw36487step2 raw36487step2Labels := by
      have ha : raw36487step2 = raw36487step1 := by apply Matrix.ext; unfold raw36487step2 raw36487step1; decide +kernel
      have hl : raw36487step1Labels = labelEmbedding6 ∘ raw36487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36487step1 raw36487step1Labels raw36487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw36488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36488step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36488 raw36488Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw36488 raw36488Labels = mixedMoment B raw36488step0 raw36488step0Labels := by
      have ha : raw36488step0 = (fun i j => raw36488 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36488step0 raw36488; decide +kernel
      have hl : raw36488step0Labels = raw36488Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36488 raw36488Labels permutation277 permutation3
    mixedMoment B raw36488step0 raw36488step0Labels = mixedMoment B raw36488step1 raw36488step1Labels := by
      have ha : raw36488step1 = raw36488step0 := by apply Matrix.ext; unfold raw36488step1 raw36488step0; decide +kernel
      have hl : raw36488step0Labels = labelEmbedding6 ∘ raw36488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36488step0 raw36488step0Labels raw36488step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw36489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36489step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36489 raw36489Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw36489 raw36489Labels = mixedMoment B raw36489step0 raw36489step0Labels := by
      have ha : raw36489step0 = (fun i j => raw36489 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36489step0 raw36489; decide +kernel
      have hl : raw36489step0Labels = raw36489Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36489 raw36489Labels permutation268 permutation3
    mixedMoment B raw36489step0 raw36489step0Labels = mixedMoment B raw36489step1 raw36489step1Labels := by
      have ha : raw36489step1 = raw36489step0 := by apply Matrix.ext; unfold raw36489step1 raw36489step0; decide +kernel
      have hl : raw36489step0Labels = labelEmbedding6 ∘ raw36489step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36489step0 raw36489step0Labels raw36489step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw36490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36490step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36490 raw36490Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw36490 raw36490Labels = mixedMoment B raw36490step0 raw36490step0Labels := by
      have ha : raw36490step0 = (fun i j => raw36490 (permutation279 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36490step0 raw36490; decide +kernel
      have hl : raw36490step0Labels = raw36490Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36490 raw36490Labels permutation279 permutation3
    mixedMoment B raw36490step0 raw36490step0Labels = mixedMoment B raw36490step1 raw36490step1Labels := by
      have ha : raw36490step1 = raw36490step0 := by apply Matrix.ext; unfold raw36490step1 raw36490step0; decide +kernel
      have hl : raw36490step0Labels = labelEmbedding6 ∘ raw36490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36490step0 raw36490step0Labels raw36490step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw36491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36491step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36491 raw36491Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36491 raw36491Labels = mixedMoment B raw36491step0 raw36491step0Labels := by
      have hz : ∀ j, raw36491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36491step0 = (fun i j => raw36491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36491step0 raw36491; decide +kernel
      have hl : raw36491step0Labels = raw36491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36491 raw36491Labels permutation434 hz
    mixedMoment B raw36491step0 raw36491step0Labels = mixedMoment B raw36491step1 raw36491step1Labels := by
      have ha : raw36491step1 = (fun i j => raw36491step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36491step1 raw36491step0; decide +kernel
      have hl : raw36491step1Labels = raw36491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36491step0 raw36491step0Labels permutation58 permutation3
    mixedMoment B raw36491step1 raw36491step1Labels = mixedMoment B raw36491step2 raw36491step2Labels := by
      have ha : raw36491step2 = raw36491step1 := by apply Matrix.ext; unfold raw36491step2 raw36491step1; decide +kernel
      have hl : raw36491step1Labels = labelEmbedding6 ∘ raw36491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36491step1 raw36491step1Labels raw36491step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36492step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36492 raw36492Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36492 raw36492Labels = mixedMoment B raw36492step0 raw36492step0Labels := by
      have ha : raw36492step0 = (fun i j => raw36492 (permutation279 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36492step0 raw36492; decide +kernel
      have hl : raw36492step0Labels = raw36492Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36492 raw36492Labels permutation279 permutation3
    mixedMoment B raw36492step0 raw36492step0Labels = mixedMoment B raw36492step1 raw36492step1Labels := by
      have ha : raw36492step1 = raw36492step0 := by apply Matrix.ext; unfold raw36492step1 raw36492step0; decide +kernel
      have hl : raw36492step0Labels = labelEmbedding6 ∘ raw36492step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36492step0 raw36492step0Labels raw36492step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36493step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36493 raw36493Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw36493 raw36493Labels = mixedMoment B raw36493step0 raw36493step0Labels := by
      have ha : raw36493step0 = (fun i j => raw36493 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36493step0 raw36493; decide +kernel
      have hl : raw36493step0Labels = raw36493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36493 raw36493Labels permutation268 permutation3
    mixedMoment B raw36493step0 raw36493step0Labels = mixedMoment B raw36493step1 raw36493step1Labels := by
      have ha : raw36493step1 = raw36493step0 := by apply Matrix.ext; unfold raw36493step1 raw36493step0; decide +kernel
      have hl : raw36493step0Labels = labelEmbedding6 ∘ raw36493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36493step0 raw36493step0Labels raw36493step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw36494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36494step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36494 raw36494Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw36494 raw36494Labels = mixedMoment B raw36494step0 raw36494step0Labels := by
      have ha : raw36494step0 = (fun i j => raw36494 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36494step0 raw36494; decide +kernel
      have hl : raw36494step0Labels = raw36494Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36494 raw36494Labels permutation268 permutation3
    mixedMoment B raw36494step0 raw36494step0Labels = mixedMoment B raw36494step1 raw36494step1Labels := by
      have ha : raw36494step1 = raw36494step0 := by apply Matrix.ext; unfold raw36494step1 raw36494step0; decide +kernel
      have hl : raw36494step0Labels = labelEmbedding6 ∘ raw36494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36494step0 raw36494step0Labels raw36494step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw36495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36495step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36495 raw36495Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36495 raw36495Labels = mixedMoment B raw36495step0 raw36495step0Labels := by
      have ha : raw36495step0 = (fun i j => raw36495 (permutation278 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36495step0 raw36495; decide +kernel
      have hl : raw36495step0Labels = raw36495Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36495 raw36495Labels permutation278 permutation3
    mixedMoment B raw36495step0 raw36495step0Labels = mixedMoment B raw36495step1 raw36495step1Labels := by
      have ha : raw36495step1 = raw36495step0 := by apply Matrix.ext; unfold raw36495step1 raw36495step0; decide +kernel
      have hl : raw36495step0Labels = labelEmbedding6 ∘ raw36495step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36495step0 raw36495step0Labels raw36495step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw36496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36496step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36496 raw36496Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw36496 raw36496Labels = mixedMoment B raw36496step0 raw36496step0Labels := by
      have ha : raw36496step0 = (fun i j => raw36496 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36496step0 raw36496; decide +kernel
      have hl : raw36496step0Labels = raw36496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36496 raw36496Labels permutation268 permutation3
    mixedMoment B raw36496step0 raw36496step0Labels = mixedMoment B raw36496step1 raw36496step1Labels := by
      have ha : raw36496step1 = raw36496step0 := by apply Matrix.ext; unfold raw36496step1 raw36496step0; decide +kernel
      have hl : raw36496step0Labels = labelEmbedding6 ∘ raw36496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36496step0 raw36496step0Labels raw36496step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw36497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36497step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36497 raw36497Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw36497 raw36497Labels = mixedMoment B raw36497step0 raw36497step0Labels := by
      have ha : raw36497step0 = (fun i j => raw36497 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36497step0 raw36497; decide +kernel
      have hl : raw36497step0Labels = raw36497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36497 raw36497Labels permutation265 permutation3
    mixedMoment B raw36497step0 raw36497step0Labels = mixedMoment B raw36497step1 raw36497step1Labels := by
      have ha : raw36497step1 = raw36497step0 := by apply Matrix.ext; unfold raw36497step1 raw36497step0; decide +kernel
      have hl : raw36497step0Labels = labelEmbedding6 ∘ raw36497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36497step0 raw36497step0Labels raw36497step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

def raw36498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36498step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36498 raw36498Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36498 raw36498Labels = mixedMoment B raw36498step0 raw36498step0Labels := by
      have ha : raw36498step0 = (fun i j => raw36498 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36498step0 raw36498; decide +kernel
      have hl : raw36498step0Labels = raw36498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36498 raw36498Labels permutation265 permutation3
    mixedMoment B raw36498step0 raw36498step0Labels = mixedMoment B raw36498step1 raw36498step1Labels := by
      have ha : raw36498step1 = raw36498step0 := by apply Matrix.ext; unfold raw36498step1 raw36498step0; decide +kernel
      have hl : raw36498step0Labels = labelEmbedding6 ∘ raw36498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36498step0 raw36498step0Labels raw36498step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw36499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36499 raw36499Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36499 raw36499Labels = mixedMoment B raw36499step0 raw36499step0Labels := by
      have ha : raw36499step0 = (fun i j => raw36499 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36499step0 raw36499; decide +kernel
      have hl : raw36499step0Labels = raw36499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36499 raw36499Labels permutation269 permutation3
    mixedMoment B raw36499step0 raw36499step0Labels = mixedMoment B raw36499step1 raw36499step1Labels := by
      have ha : raw36499step1 = raw36499step0 := by apply Matrix.ext; unfold raw36499step1 raw36499step0; decide +kernel
      have hl : raw36499step0Labels = labelEmbedding6 ∘ raw36499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36499step0 raw36499step0Labels raw36499step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36500step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36500step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36500 raw36500Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw36500 raw36500Labels = mixedMoment B raw36500step0 raw36500step0Labels := by
      have ha : raw36500step0 = (fun i j => raw36500 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36500step0 raw36500; decide +kernel
      have hl : raw36500step0Labels = raw36500Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36500 raw36500Labels permutation267 permutation3
    mixedMoment B raw36500step0 raw36500step0Labels = mixedMoment B raw36500step1 raw36500step1Labels := by
      have ha : raw36500step1 = raw36500step0 := by apply Matrix.ext; unfold raw36500step1 raw36500step0; decide +kernel
      have hl : raw36500step0Labels = labelEmbedding6 ∘ raw36500step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36500step0 raw36500step0Labels raw36500step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw36501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36501step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36501step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36501step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36501 raw36501Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw36501 raw36501Labels = mixedMoment B raw36501step0 raw36501step0Labels := by
      have ha : raw36501step0 = (fun i j => raw36501 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36501step0 raw36501; decide +kernel
      have hl : raw36501step0Labels = raw36501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36501 raw36501Labels permutation663 permutation3
    mixedMoment B raw36501step0 raw36501step0Labels = mixedMoment B raw36501step1 raw36501step1Labels := by
      have ha : raw36501step1 = -raw36501step0 := by apply Matrix.ext; change ∀ i j, raw36501step1 i j = -(raw36501step0 i j); unfold raw36501step1 raw36501step0; decide +kernel
      have hl : raw36501step1Labels = raw36501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36501step1 raw36501step1Labels = mixedMoment B raw36501step2 raw36501step2Labels := by
      have ha : raw36501step2 = raw36501step1 := by apply Matrix.ext; unfold raw36501step2 raw36501step1; decide +kernel
      have hl : raw36501step1Labels = labelEmbedding6 ∘ raw36501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36501step1 raw36501step1Labels raw36501step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw36502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36502step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36502step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36502step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36502 raw36502Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw36502 raw36502Labels = mixedMoment B raw36502step0 raw36502step0Labels := by
      have hz : ∀ j, raw36502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36502step0 = (fun i j => raw36502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36502step0 raw36502; decide +kernel
      have hl : raw36502step0Labels = raw36502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36502 raw36502Labels permutation434 hz
    mixedMoment B raw36502step0 raw36502step0Labels = mixedMoment B raw36502step1 raw36502step1Labels := by
      have ha : raw36502step1 = (fun i j => raw36502step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36502step1 raw36502step0; decide +kernel
      have hl : raw36502step1Labels = raw36502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36502step0 raw36502step0Labels permutation150 permutation3
    mixedMoment B raw36502step1 raw36502step1Labels = mixedMoment B raw36502step2 raw36502step2Labels := by
      have ha : raw36502step2 = -raw36502step1 := by apply Matrix.ext; change ∀ i j, raw36502step2 i j = -(raw36502step1 i j); unfold raw36502step2 raw36502step1; decide +kernel
      have hl : raw36502step2Labels = raw36502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36502step2 raw36502step2Labels = mixedMoment B raw36502step3 raw36502step3Labels := by
      have ha : raw36502step3 = raw36502step2 := by apply Matrix.ext; unfold raw36502step3 raw36502step2; decide +kernel
      have hl : raw36502step2Labels = labelEmbedding6 ∘ raw36502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36502step2 raw36502step2Labels raw36502step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw36503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw36503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36503step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36503step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36503step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36503step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36503 raw36503Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw36503 raw36503Labels = mixedMoment B raw36503step0 raw36503step0Labels := by
      have ha : raw36503step0 = (fun i j => raw36503 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36503step0 raw36503; decide +kernel
      have hl : raw36503step0Labels = raw36503Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36503 raw36503Labels permutation657 permutation3
    mixedMoment B raw36503step0 raw36503step0Labels = mixedMoment B raw36503step1 raw36503step1Labels := by
      have ha : raw36503step1 = -raw36503step0 := by apply Matrix.ext; change ∀ i j, raw36503step1 i j = -(raw36503step0 i j); unfold raw36503step1 raw36503step0; decide +kernel
      have hl : raw36503step1Labels = raw36503step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36503step1 raw36503step1Labels = mixedMoment B raw36503step2 raw36503step2Labels := by
      have ha : raw36503step2 = raw36503step1 := by apply Matrix.ext; unfold raw36503step2 raw36503step1; decide +kernel
      have hl : raw36503step1Labels = labelEmbedding6 ∘ raw36503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36503step1 raw36503step1Labels raw36503step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw36504 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 3, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36504step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36504step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36504 raw36504Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw36504 raw36504Labels = mixedMoment B raw36504step0 raw36504step0Labels := by
      have ha : raw36504step0 = (fun i j => raw36504 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36504step0 raw36504; decide +kernel
      have hl : raw36504step0Labels = raw36504Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36504 raw36504Labels permutation277 permutation4
    mixedMoment B raw36504step0 raw36504step0Labels = mixedMoment B raw36504step1 raw36504step1Labels := by
      have ha : raw36504step1 = -raw36504step0 := by apply Matrix.ext; change ∀ i j, raw36504step1 i j = -(raw36504step0 i j); unfold raw36504step1 raw36504step0; decide +kernel
      have hl : raw36504step1Labels = raw36504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36504step1 raw36504step1Labels = mixedMoment B raw36504step2 raw36504step2Labels := by
      have ha : raw36504step2 = raw36504step1 := by apply Matrix.ext; unfold raw36504step2 raw36504step1; decide +kernel
      have hl : raw36504step1Labels = labelEmbedding7 ∘ raw36504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36504step1 raw36504step1Labels raw36504step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw36505 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36505step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36505step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36505 raw36505Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw36505 raw36505Labels = mixedMoment B raw36505step0 raw36505step0Labels := by
      have hz : ∀ j, raw36505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36505step0 = (fun i j => raw36505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36505step0 raw36505; decide +kernel
      have hl : raw36505step0Labels = raw36505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36505 raw36505Labels permutation346 hz
    mixedMoment B raw36505step0 raw36505step0Labels = mixedMoment B raw36505step1 raw36505step1Labels := by
      have ha : raw36505step1 = (fun i j => raw36505step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36505step1 raw36505step0; decide +kernel
      have hl : raw36505step1Labels = raw36505step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36505step0 raw36505step0Labels permutation58 permutation6
    mixedMoment B raw36505step1 raw36505step1Labels = mixedMoment B raw36505step2 raw36505step2Labels := by
      have ha : raw36505step2 = raw36505step1 := by apply Matrix.ext; unfold raw36505step2 raw36505step1; decide +kernel
      have hl : raw36505step1Labels = labelEmbedding9 ∘ raw36505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36505step1 raw36505step1Labels raw36505step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw36506 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36506step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36506 raw36506Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw36506 raw36506Labels = mixedMoment B raw36506step0 raw36506step0Labels := by
      have ha : raw36506step0 = (fun i j => raw36506 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36506step0 raw36506; decide +kernel
      have hl : raw36506step0Labels = raw36506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36506 raw36506Labels permutation152 permutation7
    mixedMoment B raw36506step0 raw36506step0Labels = mixedMoment B raw36506step1 raw36506step1Labels := by
      have ha : raw36506step1 = raw36506step0 := by apply Matrix.ext; unfold raw36506step1 raw36506step0; decide +kernel
      have hl : raw36506step0Labels = labelEmbedding10 ∘ raw36506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36506step0 raw36506step0Labels raw36506step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw36507 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36507step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36507 raw36507Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw36507 raw36507Labels = mixedMoment B raw36507step0 raw36507step0Labels := by
      have ha : raw36507step0 = (fun i j => raw36507 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36507step0 raw36507; decide +kernel
      have hl : raw36507step0Labels = raw36507Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36507 raw36507Labels permutation152 permutation7
    mixedMoment B raw36507step0 raw36507step0Labels = mixedMoment B raw36507step1 raw36507step1Labels := by
      have ha : raw36507step1 = raw36507step0 := by apply Matrix.ext; unfold raw36507step1 raw36507step0; decide +kernel
      have hl : raw36507step0Labels = labelEmbedding10 ∘ raw36507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36507step0 raw36507step0Labels raw36507step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw36508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36508step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36508 raw36508Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw36508 raw36508Labels = mixedMoment B raw36508step0 raw36508step0Labels := by
      have ha : raw36508step0 = (fun i j => raw36508 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36508step0 raw36508; decide +kernel
      have hl : raw36508step0Labels = raw36508Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36508 raw36508Labels permutation152 permutation7
    mixedMoment B raw36508step0 raw36508step0Labels = mixedMoment B raw36508step1 raw36508step1Labels := by
      have ha : raw36508step1 = raw36508step0 := by apply Matrix.ext; unfold raw36508step1 raw36508step0; decide +kernel
      have hl : raw36508step0Labels = labelEmbedding10 ∘ raw36508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36508step0 raw36508step0Labels raw36508step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw36509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36509step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36509 raw36509Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw36509 raw36509Labels = mixedMoment B raw36509step0 raw36509step0Labels := by
      have ha : raw36509step0 = (fun i j => raw36509 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36509step0 raw36509; decide +kernel
      have hl : raw36509step0Labels = raw36509Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36509 raw36509Labels permutation152 permutation7
    mixedMoment B raw36509step0 raw36509step0Labels = mixedMoment B raw36509step1 raw36509step1Labels := by
      have ha : raw36509step1 = raw36509step0 := by apply Matrix.ext; unfold raw36509step1 raw36509step0; decide +kernel
      have hl : raw36509step0Labels = labelEmbedding10 ∘ raw36509step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36509step0 raw36509step0Labels raw36509step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw36510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36510step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36510step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36510 raw36510Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36510 raw36510Labels = mixedMoment B raw36510step0 raw36510step0Labels := by
      have ha : raw36510step0 = (fun i j => raw36510 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36510step0 raw36510; decide +kernel
      have hl : raw36510step0Labels = raw36510Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36510 raw36510Labels permutation687 permutation7
    mixedMoment B raw36510step0 raw36510step0Labels = mixedMoment B raw36510step1 raw36510step1Labels := by
      have ha : raw36510step1 = -raw36510step0 := by apply Matrix.ext; change ∀ i j, raw36510step1 i j = -(raw36510step0 i j); unfold raw36510step1 raw36510step0; decide +kernel
      have hl : raw36510step1Labels = raw36510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36510step1 raw36510step1Labels = mixedMoment B raw36510step2 raw36510step2Labels := by
      have ha : raw36510step2 = raw36510step1 := by apply Matrix.ext; unfold raw36510step2 raw36510step1; decide +kernel
      have hl : raw36510step1Labels = labelEmbedding10 ∘ raw36510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36510step1 raw36510step1Labels raw36510step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36511 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36511step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36511step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36511step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36511 raw36511Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36511 raw36511Labels = mixedMoment B raw36511step0 raw36511step0Labels := by
      have ha : raw36511step0 = (fun i j => raw36511 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36511step0 raw36511; decide +kernel
      have hl : raw36511step0Labels = raw36511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36511 raw36511Labels permutation167 permutation4
    mixedMoment B raw36511step0 raw36511step0Labels = mixedMoment B raw36511step1 raw36511step1Labels := by
      have ha : raw36511step1 = -raw36511step0 := by apply Matrix.ext; change ∀ i j, raw36511step1 i j = -(raw36511step0 i j); unfold raw36511step1 raw36511step0; decide +kernel
      have hl : raw36511step1Labels = raw36511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36511step1 raw36511step1Labels = mixedMoment B raw36511step2 raw36511step2Labels := by
      have ha : raw36511step2 = raw36511step1 := by apply Matrix.ext; unfold raw36511step2 raw36511step1; decide +kernel
      have hl : raw36511step1Labels = labelEmbedding7 ∘ raw36511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36511step1 raw36511step1Labels raw36511step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw36512 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36512step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36512step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36512 raw36512Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw36512 raw36512Labels = mixedMoment B raw36512step0 raw36512step0Labels := by
      have ha : raw36512step0 = (fun i j => raw36512 (permutation280 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36512step0 raw36512; decide +kernel
      have hl : raw36512step0Labels = raw36512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36512 raw36512Labels permutation280 permutation4
    mixedMoment B raw36512step0 raw36512step0Labels = mixedMoment B raw36512step1 raw36512step1Labels := by
      have ha : raw36512step1 = -raw36512step0 := by apply Matrix.ext; change ∀ i j, raw36512step1 i j = -(raw36512step0 i j); unfold raw36512step1 raw36512step0; decide +kernel
      have hl : raw36512step1Labels = raw36512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36512step1 raw36512step1Labels = mixedMoment B raw36512step2 raw36512step2Labels := by
      have ha : raw36512step2 = raw36512step1 := by apply Matrix.ext; unfold raw36512step2 raw36512step1; decide +kernel
      have hl : raw36512step1Labels = labelEmbedding7 ∘ raw36512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36512step1 raw36512step1Labels raw36512step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw36513 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36513step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36513 raw36513Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw36513 raw36513Labels = mixedMoment B raw36513step0 raw36513step0Labels := by
      have ha : raw36513step0 = (fun i j => raw36513 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36513step0 raw36513; decide +kernel
      have hl : raw36513step0Labels = raw36513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36513 raw36513Labels permutation265 permutation6
    mixedMoment B raw36513step0 raw36513step0Labels = mixedMoment B raw36513step1 raw36513step1Labels := by
      have ha : raw36513step1 = raw36513step0 := by apply Matrix.ext; unfold raw36513step1 raw36513step0; decide +kernel
      have hl : raw36513step0Labels = labelEmbedding9 ∘ raw36513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36513step0 raw36513step0Labels raw36513step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw36514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36514step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36514 raw36514Labels = mixedMoment B node5358 node5358Labels := by
  calc
    mixedMoment B raw36514 raw36514Labels = mixedMoment B raw36514step0 raw36514step0Labels := by
      have ha : raw36514step0 = (fun i j => raw36514 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36514step0 raw36514; decide +kernel
      have hl : raw36514step0Labels = raw36514Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36514 raw36514Labels permutation267 permutation6
    mixedMoment B raw36514step0 raw36514step0Labels = mixedMoment B raw36514step1 raw36514step1Labels := by
      have ha : raw36514step1 = raw36514step0 := by apply Matrix.ext; unfold raw36514step1 raw36514step0; decide +kernel
      have hl : raw36514step0Labels = labelEmbedding9 ∘ raw36514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36514step0 raw36514step0Labels raw36514step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5358 node5358Labels := by rfl

def raw36515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36515step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36515 raw36515Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw36515 raw36515Labels = mixedMoment B raw36515step0 raw36515step0Labels := by
      have ha : raw36515step0 = (fun i j => raw36515 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36515step0 raw36515; decide +kernel
      have hl : raw36515step0Labels = raw36515Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36515 raw36515Labels permutation267 permutation6
    mixedMoment B raw36515step0 raw36515step0Labels = mixedMoment B raw36515step1 raw36515step1Labels := by
      have ha : raw36515step1 = raw36515step0 := by apply Matrix.ext; unfold raw36515step1 raw36515step0; decide +kernel
      have hl : raw36515step0Labels = labelEmbedding9 ∘ raw36515step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36515step0 raw36515step0Labels raw36515step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw36516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36516step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36516step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36516 raw36516Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw36516 raw36516Labels = mixedMoment B raw36516step0 raw36516step0Labels := by
      have ha : raw36516step0 = (fun i j => raw36516 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36516step0 raw36516; decide +kernel
      have hl : raw36516step0Labels = raw36516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36516 raw36516Labels permutation165 permutation4
    mixedMoment B raw36516step0 raw36516step0Labels = mixedMoment B raw36516step1 raw36516step1Labels := by
      have ha : raw36516step1 = -raw36516step0 := by apply Matrix.ext; change ∀ i j, raw36516step1 i j = -(raw36516step0 i j); unfold raw36516step1 raw36516step0; decide +kernel
      have hl : raw36516step1Labels = raw36516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36516step1 raw36516step1Labels = mixedMoment B raw36516step2 raw36516step2Labels := by
      have ha : raw36516step2 = raw36516step1 := by apply Matrix.ext; unfold raw36516step2 raw36516step1; decide +kernel
      have hl : raw36516step1Labels = labelEmbedding7 ∘ raw36516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36516step1 raw36516step1Labels raw36516step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw36517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36517step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36517step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36517step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36517 raw36517Labels = mixedMoment B node4997 node4997Labels := by
  calc
    mixedMoment B raw36517 raw36517Labels = mixedMoment B raw36517step0 raw36517step0Labels := by
      have ha : raw36517step0 = (fun i j => raw36517 (permutation278 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36517step0 raw36517; decide +kernel
      have hl : raw36517step0Labels = raw36517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36517 raw36517Labels permutation278 permutation4
    mixedMoment B raw36517step0 raw36517step0Labels = mixedMoment B raw36517step1 raw36517step1Labels := by
      have ha : raw36517step1 = -raw36517step0 := by apply Matrix.ext; change ∀ i j, raw36517step1 i j = -(raw36517step0 i j); unfold raw36517step1 raw36517step0; decide +kernel
      have hl : raw36517step1Labels = raw36517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36517step1 raw36517step1Labels = mixedMoment B raw36517step2 raw36517step2Labels := by
      have ha : raw36517step2 = raw36517step1 := by apply Matrix.ext; unfold raw36517step2 raw36517step1; decide +kernel
      have hl : raw36517step1Labels = labelEmbedding7 ∘ raw36517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36517step1 raw36517step1Labels raw36517step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4997 node4997Labels := by rfl

def raw36518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36518step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36518 raw36518Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36518 raw36518Labels = mixedMoment B raw36518step0 raw36518step0Labels := by
      have hz : ∀ j, raw36518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36518step0 = (fun i j => raw36518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36518step0 raw36518; decide +kernel
      have hl : raw36518step0Labels = raw36518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36518 raw36518Labels permutation346 hz
    mixedMoment B raw36518step0 raw36518step0Labels = mixedMoment B raw36518step1 raw36518step1Labels := by
      have ha : raw36518step1 = (fun i j => raw36518step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36518step1 raw36518step0; decide +kernel
      have hl : raw36518step1Labels = raw36518step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36518step0 raw36518step0Labels permutation58 permutation6
    mixedMoment B raw36518step1 raw36518step1Labels = mixedMoment B raw36518step2 raw36518step2Labels := by
      have ha : raw36518step2 = raw36518step1 := by apply Matrix.ext; unfold raw36518step2 raw36518step1; decide +kernel
      have hl : raw36518step1Labels = labelEmbedding9 ∘ raw36518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36518step1 raw36518step1Labels raw36518step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw36519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36519step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36519 raw36519Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw36519 raw36519Labels = mixedMoment B raw36519step0 raw36519step0Labels := by
      have ha : raw36519step0 = (fun i j => raw36519 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36519step0 raw36519; decide +kernel
      have hl : raw36519step0Labels = raw36519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36519 raw36519Labels permutation267 permutation6
    mixedMoment B raw36519step0 raw36519step0Labels = mixedMoment B raw36519step1 raw36519step1Labels := by
      have ha : raw36519step1 = raw36519step0 := by apply Matrix.ext; unfold raw36519step1 raw36519step0; decide +kernel
      have hl : raw36519step0Labels = labelEmbedding9 ∘ raw36519step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36519step0 raw36519step0Labels raw36519step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw36520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36520step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36520 raw36520Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36520 raw36520Labels = mixedMoment B raw36520step0 raw36520step0Labels := by
      have ha : raw36520step0 = (fun i j => raw36520 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36520step0 raw36520; decide +kernel
      have hl : raw36520step0Labels = raw36520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36520 raw36520Labels permutation267 permutation6
    mixedMoment B raw36520step0 raw36520step0Labels = mixedMoment B raw36520step1 raw36520step1Labels := by
      have ha : raw36520step1 = raw36520step0 := by apply Matrix.ext; unfold raw36520step1 raw36520step0; decide +kernel
      have hl : raw36520step0Labels = labelEmbedding9 ∘ raw36520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36520step0 raw36520step0Labels raw36520step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36521step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36521 raw36521Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36521 raw36521Labels = mixedMoment B raw36521step0 raw36521step0Labels := by
      have ha : raw36521step0 = (fun i j => raw36521 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36521step0 raw36521; decide +kernel
      have hl : raw36521step0Labels = raw36521Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36521 raw36521Labels permutation152 permutation6
    mixedMoment B raw36521step0 raw36521step0Labels = mixedMoment B raw36521step1 raw36521step1Labels := by
      have ha : raw36521step1 = raw36521step0 := by apply Matrix.ext; unfold raw36521step1 raw36521step0; decide +kernel
      have hl : raw36521step0Labels = labelEmbedding9 ∘ raw36521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36521step0 raw36521step0Labels raw36521step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36522step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36522step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36522 raw36522Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw36522 raw36522Labels = mixedMoment B raw36522step0 raw36522step0Labels := by
      have ha : raw36522step0 = (fun i j => raw36522 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36522step0 raw36522; decide +kernel
      have hl : raw36522step0Labels = raw36522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36522 raw36522Labels permutation265 permutation4
    mixedMoment B raw36522step0 raw36522step0Labels = mixedMoment B raw36522step1 raw36522step1Labels := by
      have ha : raw36522step1 = -raw36522step0 := by apply Matrix.ext; change ∀ i j, raw36522step1 i j = -(raw36522step0 i j); unfold raw36522step1 raw36522step0; decide +kernel
      have hl : raw36522step1Labels = raw36522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36522step1 raw36522step1Labels = mixedMoment B raw36522step2 raw36522step2Labels := by
      have ha : raw36522step2 = raw36522step1 := by apply Matrix.ext; unfold raw36522step2 raw36522step1; decide +kernel
      have hl : raw36522step1Labels = labelEmbedding7 ∘ raw36522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36522step1 raw36522step1Labels raw36522step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw36523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36523step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36523 raw36523Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36523 raw36523Labels = mixedMoment B raw36523step0 raw36523step0Labels := by
      have hz : ∀ j, raw36523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36523step0 = (fun i j => raw36523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36523step0 raw36523; decide +kernel
      have hl : raw36523step0Labels = raw36523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36523 raw36523Labels permutation346 hz
    mixedMoment B raw36523step0 raw36523step0Labels = mixedMoment B raw36523step1 raw36523step1Labels := by
      have ha : raw36523step1 = (fun i j => raw36523step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36523step1 raw36523step0; decide +kernel
      have hl : raw36523step1Labels = raw36523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36523step0 raw36523step0Labels permutation56 permutation6
    mixedMoment B raw36523step1 raw36523step1Labels = mixedMoment B raw36523step2 raw36523step2Labels := by
      have ha : raw36523step2 = raw36523step1 := by apply Matrix.ext; unfold raw36523step2 raw36523step1; decide +kernel
      have hl : raw36523step1Labels = labelEmbedding9 ∘ raw36523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36523step1 raw36523step1Labels raw36523step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw36524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36524step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36524 raw36524Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36524 raw36524Labels = mixedMoment B raw36524step0 raw36524step0Labels := by
      have ha : raw36524step0 = (fun i j => raw36524 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36524step0 raw36524; decide +kernel
      have hl : raw36524step0Labels = raw36524Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36524 raw36524Labels permutation265 permutation6
    mixedMoment B raw36524step0 raw36524step0Labels = mixedMoment B raw36524step1 raw36524step1Labels := by
      have ha : raw36524step1 = raw36524step0 := by apply Matrix.ext; unfold raw36524step1 raw36524step0; decide +kernel
      have hl : raw36524step0Labels = labelEmbedding9 ∘ raw36524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36524step0 raw36524step0Labels raw36524step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36525 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36525step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36525 raw36525Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36525 raw36525Labels = mixedMoment B raw36525step0 raw36525step0Labels := by
      have ha : raw36525step0 = (fun i j => raw36525 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36525step0 raw36525; decide +kernel
      have hl : raw36525step0Labels = raw36525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36525 raw36525Labels permutation265 permutation6
    mixedMoment B raw36525step0 raw36525step0Labels = mixedMoment B raw36525step1 raw36525step1Labels := by
      have ha : raw36525step1 = raw36525step0 := by apply Matrix.ext; unfold raw36525step1 raw36525step0; decide +kernel
      have hl : raw36525step0Labels = labelEmbedding9 ∘ raw36525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36525step0 raw36525step0Labels raw36525step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw36526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36526step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36526 raw36526Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw36526 raw36526Labels = mixedMoment B raw36526step0 raw36526step0Labels := by
      have ha : raw36526step0 = (fun i j => raw36526 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36526step0 raw36526; decide +kernel
      have hl : raw36526step0Labels = raw36526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36526 raw36526Labels permutation164 permutation4
    mixedMoment B raw36526step0 raw36526step0Labels = mixedMoment B raw36526step1 raw36526step1Labels := by
      have ha : raw36526step1 = -raw36526step0 := by apply Matrix.ext; change ∀ i j, raw36526step1 i j = -(raw36526step0 i j); unfold raw36526step1 raw36526step0; decide +kernel
      have hl : raw36526step1Labels = raw36526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36526step1 raw36526step1Labels = mixedMoment B raw36526step2 raw36526step2Labels := by
      have ha : raw36526step2 = raw36526step1 := by apply Matrix.ext; unfold raw36526step2 raw36526step1; decide +kernel
      have hl : raw36526step1Labels = labelEmbedding7 ∘ raw36526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36526step1 raw36526step1Labels raw36526step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5323 node5323Labels := by rfl

def raw36527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw36527step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36527step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36527step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36527step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36527 raw36527Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw36527 raw36527Labels = mixedMoment B raw36527step0 raw36527step0Labels := by
      have ha : raw36527step0 = (fun i j => raw36527 (permutation277 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36527step0 raw36527; decide +kernel
      have hl : raw36527step0Labels = raw36527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36527 raw36527Labels permutation277 permutation4
    mixedMoment B raw36527step0 raw36527step0Labels = mixedMoment B raw36527step1 raw36527step1Labels := by
      have ha : raw36527step1 = -raw36527step0 := by apply Matrix.ext; change ∀ i j, raw36527step1 i j = -(raw36527step0 i j); unfold raw36527step1 raw36527step0; decide +kernel
      have hl : raw36527step1Labels = raw36527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36527step1 raw36527step1Labels = mixedMoment B raw36527step2 raw36527step2Labels := by
      have ha : raw36527step2 = raw36527step1 := by apply Matrix.ext; unfold raw36527step2 raw36527step1; decide +kernel
      have hl : raw36527step1Labels = labelEmbedding7 ∘ raw36527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36527step1 raw36527step1Labels raw36527step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw36528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36528step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36528 raw36528Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw36528 raw36528Labels = mixedMoment B raw36528step0 raw36528step0Labels := by
      have ha : raw36528step0 = (fun i j => raw36528 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36528step0 raw36528; decide +kernel
      have hl : raw36528step0Labels = raw36528Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36528 raw36528Labels permutation265 permutation6
    mixedMoment B raw36528step0 raw36528step0Labels = mixedMoment B raw36528step1 raw36528step1Labels := by
      have ha : raw36528step1 = raw36528step0 := by apply Matrix.ext; unfold raw36528step1 raw36528step0; decide +kernel
      have hl : raw36528step0Labels = labelEmbedding9 ∘ raw36528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36528step0 raw36528step0Labels raw36528step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw36529 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36529step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36529 raw36529Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36529 raw36529Labels = mixedMoment B raw36529step0 raw36529step0Labels := by
      have ha : raw36529step0 = (fun i j => raw36529 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36529step0 raw36529; decide +kernel
      have hl : raw36529step0Labels = raw36529Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36529 raw36529Labels permutation267 permutation6
    mixedMoment B raw36529step0 raw36529step0Labels = mixedMoment B raw36529step1 raw36529step1Labels := by
      have ha : raw36529step1 = raw36529step0 := by apply Matrix.ext; unfold raw36529step1 raw36529step0; decide +kernel
      have hl : raw36529step0Labels = labelEmbedding9 ∘ raw36529step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36529step0 raw36529step0Labels raw36529step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36530 raw36530Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw36530 raw36530Labels = mixedMoment B raw36530step0 raw36530step0Labels := by
      have ha : raw36530step0 = (fun i j => raw36530 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36530step0 raw36530; decide +kernel
      have hl : raw36530step0Labels = raw36530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36530 raw36530Labels permutation265 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw36531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36531 raw36531Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw36531 raw36531Labels = mixedMoment B raw36531step0 raw36531step0Labels := by
      have ha : raw36531step0 = (fun i j => raw36531 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36531step0 raw36531; decide +kernel
      have hl : raw36531step0Labels = raw36531Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36531 raw36531Labels permutation265 permutation2
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw36532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36532 raw36532Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw36532 raw36532Labels = mixedMoment B raw36532step0 raw36532step0Labels := by
      have hz : ∀ j, raw36532 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36532step0 = (fun i j => raw36532 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36532step0 raw36532; decide +kernel
      have hl : raw36532step0Labels = raw36532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36532 raw36532Labels permutation520 hz
    mixedMoment B raw36532step0 raw36532step0Labels = mixedMoment B raw36532step1 raw36532step1Labels := by
      have ha : raw36532step1 = (fun i j => raw36532step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36532step1 raw36532step0; decide +kernel
      have hl : raw36532step1Labels = raw36532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36532step0 raw36532step0Labels permutation56 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw36533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36533step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36533step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36533 raw36533Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw36533 raw36533Labels = mixedMoment B raw36533step0 raw36533step0Labels := by
      have ha : raw36533step0 = (fun i j => raw36533 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36533step0 raw36533; decide +kernel
      have hl : raw36533step0Labels = raw36533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36533 raw36533Labels permutation273 permutation7
    mixedMoment B raw36533step0 raw36533step0Labels = mixedMoment B raw36533step1 raw36533step1Labels := by
      have ha : raw36533step1 = -raw36533step0 := by apply Matrix.ext; change ∀ i j, raw36533step1 i j = -(raw36533step0 i j); unfold raw36533step1 raw36533step0; decide +kernel
      have hl : raw36533step1Labels = raw36533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36533step1 raw36533step1Labels = mixedMoment B raw36533step2 raw36533step2Labels := by
      have ha : raw36533step2 = raw36533step1 := by apply Matrix.ext; unfold raw36533step2 raw36533step1; decide +kernel
      have hl : raw36533step1Labels = labelEmbedding10 ∘ raw36533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36533step1 raw36533step1Labels raw36533step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw36534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36534 raw36534Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw36534 raw36534Labels = mixedMoment B raw36534step0 raw36534step0Labels := by
      have hz : ∀ j, raw36534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36534step0 = (fun i j => raw36534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36534step0 raw36534; decide +kernel
      have hl : raw36534step0Labels = raw36534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36534 raw36534Labels permutation434 hz
    mixedMoment B raw36534step0 raw36534step0Labels = mixedMoment B raw36534step1 raw36534step1Labels := by
      have ha : raw36534step1 = (fun i j => raw36534step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36534step1 raw36534step0; decide +kernel
      have hl : raw36534step1Labels = raw36534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36534step0 raw36534step0Labels permutation151 permutation2
    mixedMoment B raw36534step1 raw36534step1Labels = mixedMoment B raw36534step2 raw36534step2Labels := by
      have ha : raw36534step2 = -raw36534step1 := by apply Matrix.ext; change ∀ i j, raw36534step2 i j = -(raw36534step1 i j); unfold raw36534step2 raw36534step1; decide +kernel
      have hl : raw36534step2Labels = raw36534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw36535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36535step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36535 raw36535Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw36535 raw36535Labels = mixedMoment B raw36535step0 raw36535step0Labels := by
      have ha : raw36535step0 = (fun i j => raw36535 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36535step0 raw36535; decide +kernel
      have hl : raw36535step0Labels = raw36535Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36535 raw36535Labels permutation152 permutation3
    mixedMoment B raw36535step0 raw36535step0Labels = mixedMoment B raw36535step1 raw36535step1Labels := by
      have ha : raw36535step1 = raw36535step0 := by apply Matrix.ext; unfold raw36535step1 raw36535step0; decide +kernel
      have hl : raw36535step0Labels = labelEmbedding6 ∘ raw36535step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36535step0 raw36535step0Labels raw36535step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw36536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36536 raw36536Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw36536 raw36536Labels = mixedMoment B raw36536step0 raw36536step0Labels := by
      have ha : raw36536step0 = (fun i j => raw36536 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36536step0 raw36536; decide +kernel
      have hl : raw36536step0Labels = raw36536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36536 raw36536Labels permutation273 permutation2
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw36537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36537 raw36537Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36537 raw36537Labels = mixedMoment B raw36537step0 raw36537step0Labels := by
      have hz : ∀ j, raw36537 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36537step0 = (fun i j => raw36537 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36537step0 raw36537; decide +kernel
      have hl : raw36537step0Labels = raw36537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36537 raw36537Labels permutation520 hz
    mixedMoment B raw36537step0 raw36537step0Labels = mixedMoment B raw36537step1 raw36537step1Labels := by
      have ha : raw36537step1 = (fun i j => raw36537step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36537step1 raw36537step0; decide +kernel
      have hl : raw36537step1Labels = raw36537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36537step0 raw36537step0Labels permutation58 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36538 raw36538Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36538 raw36538Labels = mixedMoment B raw36538step0 raw36538step0Labels := by
      have ha : raw36538step0 = (fun i j => raw36538 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36538step0 raw36538; decide +kernel
      have hl : raw36538step0Labels = raw36538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36538 raw36538Labels permutation273 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36539step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36539 raw36539Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw36539 raw36539Labels = mixedMoment B raw36539step0 raw36539step0Labels := by
      have ha : raw36539step0 = (fun i j => raw36539 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36539step0 raw36539; decide +kernel
      have hl : raw36539step0Labels = raw36539Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36539 raw36539Labels permutation155 permutation3
    mixedMoment B raw36539step0 raw36539step0Labels = mixedMoment B raw36539step1 raw36539step1Labels := by
      have ha : raw36539step1 = raw36539step0 := by apply Matrix.ext; unfold raw36539step1 raw36539step0; decide +kernel
      have hl : raw36539step0Labels = labelEmbedding6 ∘ raw36539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36539step0 raw36539step0Labels raw36539step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw36540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36540 raw36540Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw36540 raw36540Labels = mixedMoment B raw36540step0 raw36540step0Labels := by
      have ha : raw36540step0 = (fun i j => raw36540 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36540step0 raw36540; decide +kernel
      have hl : raw36540step0Labels = raw36540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36540 raw36540Labels permutation267 permutation2
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw36541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36541 raw36541Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw36541 raw36541Labels = mixedMoment B raw36541step0 raw36541step0Labels := by
      have ha : raw36541step0 = (fun i j => raw36541 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36541step0 raw36541; decide +kernel
      have hl : raw36541step0Labels = raw36541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36541 raw36541Labels permutation267 permutation2
    _ = mixedMoment B node5339 node5339Labels := by rfl

def raw36542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36542 raw36542Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36542 raw36542Labels = mixedMoment B raw36542step0 raw36542step0Labels := by
      have hz : ∀ j, raw36542 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36542step0 = (fun i j => raw36542 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36542step0 raw36542; decide +kernel
      have hl : raw36542step0Labels = raw36542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36542 raw36542Labels permutation520 hz
    mixedMoment B raw36542step0 raw36542step0Labels = mixedMoment B raw36542step1 raw36542step1Labels := by
      have ha : raw36542step1 = (fun i j => raw36542step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36542step1 raw36542step0; decide +kernel
      have hl : raw36542step1Labels = raw36542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36542step0 raw36542step0Labels permutation56 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw36543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36543 raw36543Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36543 raw36543Labels = mixedMoment B raw36543step0 raw36543step0Labels := by
      have ha : raw36543step0 = (fun i j => raw36543 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36543step0 raw36543; decide +kernel
      have hl : raw36543step0Labels = raw36543Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36543 raw36543Labels permutation268 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36544step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36544 raw36544Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw36544 raw36544Labels = mixedMoment B raw36544step0 raw36544step0Labels := by
      have ha : raw36544step0 = (fun i j => raw36544 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36544step0 raw36544; decide +kernel
      have hl : raw36544step0Labels = raw36544Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36544 raw36544Labels permutation153 permutation3
    mixedMoment B raw36544step0 raw36544step0Labels = mixedMoment B raw36544step1 raw36544step1Labels := by
      have ha : raw36544step1 = raw36544step0 := by apply Matrix.ext; unfold raw36544step1 raw36544step0; decide +kernel
      have hl : raw36544step0Labels = labelEmbedding6 ∘ raw36544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36544step0 raw36544step0Labels raw36544step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw36545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36545 raw36545Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw36545 raw36545Labels = mixedMoment B raw36545step0 raw36545step0Labels := by
      have ha : raw36545step0 = (fun i j => raw36545 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36545step0 raw36545; decide +kernel
      have hl : raw36545step0Labels = raw36545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36545 raw36545Labels permutation265 permutation2
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw36546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36546 raw36546Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw36546 raw36546Labels = mixedMoment B raw36546step0 raw36546step0Labels := by
      have ha : raw36546step0 = (fun i j => raw36546 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36546step0 raw36546; decide +kernel
      have hl : raw36546step0Labels = raw36546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36546 raw36546Labels permutation265 permutation2
    _ = mixedMoment B node5339 node5339Labels := by rfl

def raw36547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw36547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36547 raw36547Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36547 raw36547Labels = mixedMoment B raw36547step0 raw36547step0Labels := by
      have ha : raw36547step0 = (fun i j => raw36547 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36547step0 raw36547; decide +kernel
      have hl : raw36547step0Labels = raw36547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36547 raw36547Labels permutation266 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36548step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36548 raw36548Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw36548 raw36548Labels = mixedMoment B raw36548step0 raw36548step0Labels := by
      have ha : raw36548step0 = (fun i j => raw36548 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36548step0 raw36548; decide +kernel
      have hl : raw36548step0Labels = raw36548Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36548 raw36548Labels permutation152 permutation3
    mixedMoment B raw36548step0 raw36548step0Labels = mixedMoment B raw36548step1 raw36548step1Labels := by
      have ha : raw36548step1 = raw36548step0 := by apply Matrix.ext; unfold raw36548step1 raw36548step0; decide +kernel
      have hl : raw36548step0Labels = labelEmbedding6 ∘ raw36548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36548step0 raw36548step0Labels raw36548step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw36549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36549 raw36549Labels = mixedMoment B node4929 node4929Labels := by
  calc
    mixedMoment B raw36549 raw36549Labels = mixedMoment B raw36549step0 raw36549step0Labels := by
      have ha : raw36549step0 = (fun i j => raw36549 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36549step0 raw36549; decide +kernel
      have hl : raw36549step0Labels = raw36549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36549 raw36549Labels permutation265 permutation2
    _ = mixedMoment B node4929 node4929Labels := by rfl

def raw36550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36550 raw36550Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw36550 raw36550Labels = mixedMoment B raw36550step0 raw36550step0Labels := by
      have ha : raw36550step0 = (fun i j => raw36550 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36550step0 raw36550; decide +kernel
      have hl : raw36550step0Labels = raw36550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36550 raw36550Labels permutation663 permutation2
    mixedMoment B raw36550step0 raw36550step0Labels = mixedMoment B raw36550step1 raw36550step1Labels := by
      have ha : raw36550step1 = -raw36550step0 := by apply Matrix.ext; change ∀ i j, raw36550step1 i j = -(raw36550step0 i j); unfold raw36550step1 raw36550step0; decide +kernel
      have hl : raw36550step1Labels = raw36550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5112 node5112Labels := by rfl

def raw36551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36551 raw36551Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw36551 raw36551Labels = mixedMoment B raw36551step0 raw36551step0Labels := by
      have hz : ∀ j, raw36551 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36551step0 = (fun i j => raw36551 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36551step0 raw36551; decide +kernel
      have hl : raw36551step0Labels = raw36551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36551 raw36551Labels permutation520 hz
    mixedMoment B raw36551step0 raw36551step0Labels = mixedMoment B raw36551step1 raw36551step1Labels := by
      have ha : raw36551step1 = (fun i j => raw36551step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36551step1 raw36551step0; decide +kernel
      have hl : raw36551step1Labels = raw36551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36551step0 raw36551step0Labels permutation150 permutation2
    mixedMoment B raw36551step1 raw36551step1Labels = mixedMoment B raw36551step2 raw36551step2Labels := by
      have ha : raw36551step2 = -raw36551step1 := by apply Matrix.ext; change ∀ i j, raw36551step2 i j = -(raw36551step1 i j); unfold raw36551step2 raw36551step1; decide +kernel
      have hl : raw36551step2Labels = raw36551step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw36552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36552 raw36552Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw36552 raw36552Labels = mixedMoment B raw36552step0 raw36552step0Labels := by
      have ha : raw36552step0 = (fun i j => raw36552 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36552step0 raw36552; decide +kernel
      have hl : raw36552step0Labels = raw36552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36552 raw36552Labels permutation273 permutation7
    mixedMoment B raw36552step0 raw36552step0Labels = mixedMoment B raw36552step1 raw36552step1Labels := by
      have ha : raw36552step1 = -raw36552step0 := by apply Matrix.ext; change ∀ i j, raw36552step1 i j = -(raw36552step0 i j); unfold raw36552step1 raw36552step0; decide +kernel
      have hl : raw36552step1Labels = raw36552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36552step1 raw36552step1Labels = mixedMoment B raw36552step2 raw36552step2Labels := by
      have ha : raw36552step2 = raw36552step1 := by apply Matrix.ext; unfold raw36552step2 raw36552step1; decide +kernel
      have hl : raw36552step1Labels = labelEmbedding1 ∘ raw36552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36552step1 raw36552step1Labels raw36552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw36553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw36553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36553step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36553step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36553 raw36553Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw36553 raw36553Labels = mixedMoment B raw36553step0 raw36553step0Labels := by
      have ha : raw36553step0 = (fun i j => raw36553 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36553step0 raw36553; decide +kernel
      have hl : raw36553step0Labels = raw36553Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36553 raw36553Labels permutation273 permutation7
    mixedMoment B raw36553step0 raw36553step0Labels = mixedMoment B raw36553step1 raw36553step1Labels := by
      have ha : raw36553step1 = -raw36553step0 := by apply Matrix.ext; change ∀ i j, raw36553step1 i j = -(raw36553step0 i j); unfold raw36553step1 raw36553step0; decide +kernel
      have hl : raw36553step1Labels = raw36553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36553step1 raw36553step1Labels = mixedMoment B raw36553step2 raw36553step2Labels := by
      have ha : raw36553step2 = raw36553step1 := by apply Matrix.ext; unfold raw36553step2 raw36553step1; decide +kernel
      have hl : raw36553step1Labels = labelEmbedding1 ∘ raw36553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36553step1 raw36553step1Labels raw36553step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw36554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw36554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36554step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36554 raw36554Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw36554 raw36554Labels = mixedMoment B raw36554step0 raw36554step0Labels := by
      have hz : ∀ j, raw36554 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36554step0 = (fun i j => raw36554 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36554step0 raw36554; decide +kernel
      have hl : raw36554step0Labels = raw36554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36554 raw36554Labels permutation520 hz
    mixedMoment B raw36554step0 raw36554step0Labels = mixedMoment B raw36554step1 raw36554step1Labels := by
      have ha : raw36554step1 = (fun i j => raw36554step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36554step1 raw36554step0; decide +kernel
      have hl : raw36554step1Labels = raw36554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36554step0 raw36554step0Labels permutation58 permutation7
    mixedMoment B raw36554step1 raw36554step1Labels = mixedMoment B raw36554step2 raw36554step2Labels := by
      have ha : raw36554step2 = -raw36554step1 := by apply Matrix.ext; change ∀ i j, raw36554step2 i j = -(raw36554step1 i j); unfold raw36554step2 raw36554step1; decide +kernel
      have hl : raw36554step2Labels = raw36554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36554step2 raw36554step2Labels = mixedMoment B raw36554step3 raw36554step3Labels := by
      have ha : raw36554step3 = raw36554step2 := by apply Matrix.ext; unfold raw36554step3 raw36554step2; decide +kernel
      have hl : raw36554step2Labels = labelEmbedding1 ∘ raw36554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36554step2 raw36554step2Labels raw36554step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw36555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36555step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36555step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36555 raw36555Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw36555 raw36555Labels = mixedMoment B raw36555step0 raw36555step0Labels := by
      have ha : raw36555step0 = (fun i j => raw36555 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36555step0 raw36555; decide +kernel
      have hl : raw36555step0Labels = raw36555Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36555 raw36555Labels permutation273 permutation7
    mixedMoment B raw36555step0 raw36555step0Labels = mixedMoment B raw36555step1 raw36555step1Labels := by
      have ha : raw36555step1 = -raw36555step0 := by apply Matrix.ext; change ∀ i j, raw36555step1 i j = -(raw36555step0 i j); unfold raw36555step1 raw36555step0; decide +kernel
      have hl : raw36555step1Labels = raw36555step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36555step1 raw36555step1Labels = mixedMoment B raw36555step2 raw36555step2Labels := by
      have ha : raw36555step2 = raw36555step1 := by apply Matrix.ext; unfold raw36555step2 raw36555step1; decide +kernel
      have hl : raw36555step1Labels = labelEmbedding1 ∘ raw36555step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36555step1 raw36555step1Labels raw36555step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw36556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36556step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36556 raw36556Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw36556 raw36556Labels = mixedMoment B raw36556step0 raw36556step0Labels := by
      have hz : ∀ j, raw36556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36556step0 = (fun i j => raw36556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36556step0 raw36556; decide +kernel
      have hl : raw36556step0Labels = raw36556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36556 raw36556Labels permutation434 hz
    mixedMoment B raw36556step0 raw36556step0Labels = mixedMoment B raw36556step1 raw36556step1Labels := by
      have ha : raw36556step1 = (fun i j => raw36556step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36556step1 raw36556step0; decide +kernel
      have hl : raw36556step1Labels = raw36556step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36556step0 raw36556step0Labels permutation144 permutation7
    mixedMoment B raw36556step1 raw36556step1Labels = mixedMoment B raw36556step2 raw36556step2Labels := by
      have ha : raw36556step2 = raw36556step1 := by apply Matrix.ext; unfold raw36556step2 raw36556step1; decide +kernel
      have hl : raw36556step1Labels = labelEmbedding1 ∘ raw36556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36556step1 raw36556step1Labels raw36556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw36557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw36557step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36557step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36557step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36557 raw36557Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw36557 raw36557Labels = mixedMoment B raw36557step0 raw36557step0Labels := by
      have ha : raw36557step0 = (fun i j => raw36557 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36557step0 raw36557; decide +kernel
      have hl : raw36557step0Labels = raw36557Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36557 raw36557Labels permutation156 permutation5
    mixedMoment B raw36557step0 raw36557step0Labels = mixedMoment B raw36557step1 raw36557step1Labels := by
      have ha : raw36557step1 = -raw36557step0 := by apply Matrix.ext; change ∀ i j, raw36557step1 i j = -(raw36557step0 i j); unfold raw36557step1 raw36557step0; decide +kernel
      have hl : raw36557step1Labels = raw36557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36557step1 raw36557step1Labels = mixedMoment B raw36557step2 raw36557step2Labels := by
      have ha : raw36557step2 = raw36557step1 := by apply Matrix.ext; unfold raw36557step2 raw36557step1; decide +kernel
      have hl : raw36557step1Labels = labelEmbedding1 ∘ raw36557step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36557step1 raw36557step1Labels raw36557step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

def raw36558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36558step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36558 raw36558Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw36558 raw36558Labels = mixedMoment B raw36558step0 raw36558step0Labels := by
      have ha : raw36558step0 = (fun i j => raw36558 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36558step0 raw36558; decide +kernel
      have hl : raw36558step0Labels = raw36558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36558 raw36558Labels permutation273 permutation7
    mixedMoment B raw36558step0 raw36558step0Labels = mixedMoment B raw36558step1 raw36558step1Labels := by
      have ha : raw36558step1 = -raw36558step0 := by apply Matrix.ext; change ∀ i j, raw36558step1 i j = -(raw36558step0 i j); unfold raw36558step1 raw36558step0; decide +kernel
      have hl : raw36558step1Labels = raw36558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36558step1 raw36558step1Labels = mixedMoment B raw36558step2 raw36558step2Labels := by
      have ha : raw36558step2 = raw36558step1 := by apply Matrix.ext; unfold raw36558step2 raw36558step1; decide +kernel
      have hl : raw36558step1Labels = labelEmbedding1 ∘ raw36558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36558step1 raw36558step1Labels raw36558step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

def raw36559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36559step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36559step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36559step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36559 raw36559Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw36559 raw36559Labels = mixedMoment B raw36559step0 raw36559step0Labels := by
      have hz : ∀ j, raw36559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36559step0 = (fun i j => raw36559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36559step0 raw36559; decide +kernel
      have hl : raw36559step0Labels = raw36559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36559 raw36559Labels permutation520 hz
    mixedMoment B raw36559step0 raw36559step0Labels = mixedMoment B raw36559step1 raw36559step1Labels := by
      have ha : raw36559step1 = (fun i j => raw36559step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36559step1 raw36559step0; decide +kernel
      have hl : raw36559step1Labels = raw36559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36559step0 raw36559step0Labels permutation58 permutation7
    mixedMoment B raw36559step1 raw36559step1Labels = mixedMoment B raw36559step2 raw36559step2Labels := by
      have ha : raw36559step2 = -raw36559step1 := by apply Matrix.ext; change ∀ i j, raw36559step2 i j = -(raw36559step1 i j); unfold raw36559step2 raw36559step1; decide +kernel
      have hl : raw36559step2Labels = raw36559step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36559step2 raw36559step2Labels = mixedMoment B raw36559step3 raw36559step3Labels := by
      have ha : raw36559step3 = raw36559step2 := by apply Matrix.ext; unfold raw36559step3 raw36559step2; decide +kernel
      have hl : raw36559step2Labels = labelEmbedding1 ∘ raw36559step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36559step2 raw36559step2Labels raw36559step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw36560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36560step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36560 raw36560Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw36560 raw36560Labels = mixedMoment B raw36560step0 raw36560step0Labels := by
      have ha : raw36560step0 = (fun i j => raw36560 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36560step0 raw36560; decide +kernel
      have hl : raw36560step0Labels = raw36560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36560 raw36560Labels permutation273 permutation7
    mixedMoment B raw36560step0 raw36560step0Labels = mixedMoment B raw36560step1 raw36560step1Labels := by
      have ha : raw36560step1 = -raw36560step0 := by apply Matrix.ext; change ∀ i j, raw36560step1 i j = -(raw36560step0 i j); unfold raw36560step1 raw36560step0; decide +kernel
      have hl : raw36560step1Labels = raw36560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36560step1 raw36560step1Labels = mixedMoment B raw36560step2 raw36560step2Labels := by
      have ha : raw36560step2 = raw36560step1 := by apply Matrix.ext; unfold raw36560step2 raw36560step1; decide +kernel
      have hl : raw36560step1Labels = labelEmbedding1 ∘ raw36560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36560step1 raw36560step1Labels raw36560step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw36561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36561 raw36561Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw36561 raw36561Labels = mixedMoment B raw36561step0 raw36561step0Labels := by
      have ha : raw36561step0 = (fun i j => raw36561 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36561step0 raw36561; decide +kernel
      have hl : raw36561step0Labels = raw36561Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36561 raw36561Labels permutation181 permutation5
    mixedMoment B raw36561step0 raw36561step0Labels = mixedMoment B raw36561step1 raw36561step1Labels := by
      have ha : raw36561step1 = -raw36561step0 := by apply Matrix.ext; change ∀ i j, raw36561step1 i j = -(raw36561step0 i j); unfold raw36561step1 raw36561step0; decide +kernel
      have hl : raw36561step1Labels = raw36561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36561step1 raw36561step1Labels = mixedMoment B raw36561step2 raw36561step2Labels := by
      have ha : raw36561step2 = raw36561step1 := by apply Matrix.ext; unfold raw36561step2 raw36561step1; decide +kernel
      have hl : raw36561step1Labels = labelEmbedding1 ∘ raw36561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36561step1 raw36561step1Labels raw36561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw36562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36562step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36562 raw36562Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36562 raw36562Labels = mixedMoment B raw36562step0 raw36562step0Labels := by
      have ha : raw36562step0 = (fun i j => raw36562 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36562step0 raw36562; decide +kernel
      have hl : raw36562step0Labels = raw36562Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36562 raw36562Labels permutation279 permutation7
    mixedMoment B raw36562step0 raw36562step0Labels = mixedMoment B raw36562step1 raw36562step1Labels := by
      have ha : raw36562step1 = -raw36562step0 := by apply Matrix.ext; change ∀ i j, raw36562step1 i j = -(raw36562step0 i j); unfold raw36562step1 raw36562step0; decide +kernel
      have hl : raw36562step1Labels = raw36562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36562step1 raw36562step1Labels = mixedMoment B raw36562step2 raw36562step2Labels := by
      have ha : raw36562step2 = raw36562step1 := by apply Matrix.ext; unfold raw36562step2 raw36562step1; decide +kernel
      have hl : raw36562step1Labels = labelEmbedding1 ∘ raw36562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36562step1 raw36562step1Labels raw36562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw36563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw36563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36563step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36563step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36563 raw36563Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw36563 raw36563Labels = mixedMoment B raw36563step0 raw36563step0Labels := by
      have ha : raw36563step0 = (fun i j => raw36563 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36563step0 raw36563; decide +kernel
      have hl : raw36563step0Labels = raw36563Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36563 raw36563Labels permutation279 permutation7
    mixedMoment B raw36563step0 raw36563step0Labels = mixedMoment B raw36563step1 raw36563step1Labels := by
      have ha : raw36563step1 = -raw36563step0 := by apply Matrix.ext; change ∀ i j, raw36563step1 i j = -(raw36563step0 i j); unfold raw36563step1 raw36563step0; decide +kernel
      have hl : raw36563step1Labels = raw36563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36563step1 raw36563step1Labels = mixedMoment B raw36563step2 raw36563step2Labels := by
      have ha : raw36563step2 = raw36563step1 := by apply Matrix.ext; unfold raw36563step2 raw36563step1; decide +kernel
      have hl : raw36563step1Labels = labelEmbedding1 ∘ raw36563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36563step1 raw36563step1Labels raw36563step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

def raw36564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36564step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36564step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36564 raw36564Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw36564 raw36564Labels = mixedMoment B raw36564step0 raw36564step0Labels := by
      have hz : ∀ j, raw36564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36564step0 = (fun i j => raw36564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36564step0 raw36564; decide +kernel
      have hl : raw36564step0Labels = raw36564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36564 raw36564Labels permutation520 hz
    mixedMoment B raw36564step0 raw36564step0Labels = mixedMoment B raw36564step1 raw36564step1Labels := by
      have ha : raw36564step1 = (fun i j => raw36564step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36564step1 raw36564step0; decide +kernel
      have hl : raw36564step1Labels = raw36564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36564step0 raw36564step0Labels permutation58 permutation7
    mixedMoment B raw36564step1 raw36564step1Labels = mixedMoment B raw36564step2 raw36564step2Labels := by
      have ha : raw36564step2 = -raw36564step1 := by apply Matrix.ext; change ∀ i j, raw36564step2 i j = -(raw36564step1 i j); unfold raw36564step2 raw36564step1; decide +kernel
      have hl : raw36564step2Labels = raw36564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36564step2 raw36564step2Labels = mixedMoment B raw36564step3 raw36564step3Labels := by
      have ha : raw36564step3 = raw36564step2 := by apply Matrix.ext; unfold raw36564step3 raw36564step2; decide +kernel
      have hl : raw36564step2Labels = labelEmbedding1 ∘ raw36564step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36564step2 raw36564step2Labels raw36564step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw36565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36565step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36565 raw36565Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36565 raw36565Labels = mixedMoment B raw36565step0 raw36565step0Labels := by
      have ha : raw36565step0 = (fun i j => raw36565 (permutation279 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36565step0 raw36565; decide +kernel
      have hl : raw36565step0Labels = raw36565Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36565 raw36565Labels permutation279 permutation7
    mixedMoment B raw36565step0 raw36565step0Labels = mixedMoment B raw36565step1 raw36565step1Labels := by
      have ha : raw36565step1 = -raw36565step0 := by apply Matrix.ext; change ∀ i j, raw36565step1 i j = -(raw36565step0 i j); unfold raw36565step1 raw36565step0; decide +kernel
      have hl : raw36565step1Labels = raw36565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36565step1 raw36565step1Labels = mixedMoment B raw36565step2 raw36565step2Labels := by
      have ha : raw36565step2 = raw36565step1 := by apply Matrix.ext; unfold raw36565step2 raw36565step1; decide +kernel
      have hl : raw36565step1Labels = labelEmbedding1 ∘ raw36565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36565step1 raw36565step1Labels raw36565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw36566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw36566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw36566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36566 raw36566Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw36566 raw36566Labels = mixedMoment B raw36566step0 raw36566step0Labels := by
      have ha : raw36566step0 = (fun i j => raw36566 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36566step0 raw36566; decide +kernel
      have hl : raw36566step0Labels = raw36566Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36566 raw36566Labels permutation180 permutation5
    mixedMoment B raw36566step0 raw36566step0Labels = mixedMoment B raw36566step1 raw36566step1Labels := by
      have ha : raw36566step1 = -raw36566step0 := by apply Matrix.ext; change ∀ i j, raw36566step1 i j = -(raw36566step0 i j); unfold raw36566step1 raw36566step0; decide +kernel
      have hl : raw36566step1Labels = raw36566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36566step1 raw36566step1Labels = mixedMoment B raw36566step2 raw36566step2Labels := by
      have ha : raw36566step2 = raw36566step1 := by apply Matrix.ext; unfold raw36566step2 raw36566step1; decide +kernel
      have hl : raw36566step1Labels = labelEmbedding1 ∘ raw36566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36566step1 raw36566step1Labels raw36566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw36567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36567step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36567 raw36567Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36567 raw36567Labels = mixedMoment B raw36567step0 raw36567step0Labels := by
      have ha : raw36567step0 = (fun i j => raw36567 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36567step0 raw36567; decide +kernel
      have hl : raw36567step0Labels = raw36567Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36567 raw36567Labels permutation273 permutation7
    mixedMoment B raw36567step0 raw36567step0Labels = mixedMoment B raw36567step1 raw36567step1Labels := by
      have ha : raw36567step1 = -raw36567step0 := by apply Matrix.ext; change ∀ i j, raw36567step1 i j = -(raw36567step0 i j); unfold raw36567step1 raw36567step0; decide +kernel
      have hl : raw36567step1Labels = raw36567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36567step1 raw36567step1Labels = mixedMoment B raw36567step2 raw36567step2Labels := by
      have ha : raw36567step2 = raw36567step1 := by apply Matrix.ext; unfold raw36567step2 raw36567step1; decide +kernel
      have hl : raw36567step1Labels = labelEmbedding1 ∘ raw36567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36567step1 raw36567step1Labels raw36567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw36568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw36568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw36568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36568 raw36568Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw36568 raw36568Labels = mixedMoment B raw36568step0 raw36568step0Labels := by
      have ha : raw36568step0 = (fun i j => raw36568 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36568step0 raw36568; decide +kernel
      have hl : raw36568step0Labels = raw36568Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36568 raw36568Labels permutation273 permutation7
    mixedMoment B raw36568step0 raw36568step0Labels = mixedMoment B raw36568step1 raw36568step1Labels := by
      have ha : raw36568step1 = -raw36568step0 := by apply Matrix.ext; change ∀ i j, raw36568step1 i j = -(raw36568step0 i j); unfold raw36568step1 raw36568step0; decide +kernel
      have hl : raw36568step1Labels = raw36568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36568step1 raw36568step1Labels = mixedMoment B raw36568step2 raw36568step2Labels := by
      have ha : raw36568step2 = raw36568step1 := by apply Matrix.ext; unfold raw36568step2 raw36568step1; decide +kernel
      have hl : raw36568step1Labels = labelEmbedding1 ∘ raw36568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36568step1 raw36568step1Labels raw36568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

def raw36569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw36569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36569step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36569step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36569 raw36569Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw36569 raw36569Labels = mixedMoment B raw36569step0 raw36569step0Labels := by
      have ha : raw36569step0 = (fun i j => raw36569 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36569step0 raw36569; decide +kernel
      have hl : raw36569step0Labels = raw36569Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36569 raw36569Labels permutation273 permutation7
    mixedMoment B raw36569step0 raw36569step0Labels = mixedMoment B raw36569step1 raw36569step1Labels := by
      have ha : raw36569step1 = -raw36569step0 := by apply Matrix.ext; change ∀ i j, raw36569step1 i j = -(raw36569step0 i j); unfold raw36569step1 raw36569step0; decide +kernel
      have hl : raw36569step1Labels = raw36569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36569step1 raw36569step1Labels = mixedMoment B raw36569step2 raw36569step2Labels := by
      have ha : raw36569step2 = raw36569step1 := by apply Matrix.ext; unfold raw36569step2 raw36569step1; decide +kernel
      have hl : raw36569step1Labels = labelEmbedding1 ∘ raw36569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36569step1 raw36569step1Labels raw36569step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw36570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw36570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw36570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36570 raw36570Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw36570 raw36570Labels = mixedMoment B raw36570step0 raw36570step0Labels := by
      have ha : raw36570step0 = (fun i j => raw36570 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36570step0 raw36570; decide +kernel
      have hl : raw36570step0Labels = raw36570Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36570 raw36570Labels permutation176 permutation5
    mixedMoment B raw36570step0 raw36570step0Labels = mixedMoment B raw36570step1 raw36570step1Labels := by
      have ha : raw36570step1 = -raw36570step0 := by apply Matrix.ext; change ∀ i j, raw36570step1 i j = -(raw36570step0 i j); unfold raw36570step1 raw36570step0; decide +kernel
      have hl : raw36570step1Labels = raw36570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36570step1 raw36570step1Labels = mixedMoment B raw36570step2 raw36570step2Labels := by
      have ha : raw36570step2 = raw36570step1 := by apply Matrix.ext; unfold raw36570step2 raw36570step1; decide +kernel
      have hl : raw36570step1Labels = labelEmbedding1 ∘ raw36570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36570step1 raw36570step1Labels raw36570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw36571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw36571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36571 raw36571Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw36571 raw36571Labels = mixedMoment B raw36571step0 raw36571step0Labels := by
      have ha : raw36571step0 = (fun i j => raw36571 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36571step0 raw36571; decide +kernel
      have hl : raw36571step0Labels = raw36571Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36571 raw36571Labels permutation273 permutation7
    mixedMoment B raw36571step0 raw36571step0Labels = mixedMoment B raw36571step1 raw36571step1Labels := by
      have ha : raw36571step1 = -raw36571step0 := by apply Matrix.ext; change ∀ i j, raw36571step1 i j = -(raw36571step0 i j); unfold raw36571step1 raw36571step0; decide +kernel
      have hl : raw36571step1Labels = raw36571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36571step1 raw36571step1Labels = mixedMoment B raw36571step2 raw36571step2Labels := by
      have ha : raw36571step2 = raw36571step1 := by apply Matrix.ext; unfold raw36571step2 raw36571step1; decide +kernel
      have hl : raw36571step1Labels = labelEmbedding1 ∘ raw36571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36571step1 raw36571step1Labels raw36571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

def raw36572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36572 raw36572Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw36572 raw36572Labels = mixedMoment B raw36572step0 raw36572step0Labels := by
      have ha : raw36572step0 = (fun i j => raw36572 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36572step0 raw36572; decide +kernel
      have hl : raw36572step0Labels = raw36572Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36572 raw36572Labels permutation639 permutation7
    mixedMoment B raw36572step0 raw36572step0Labels = mixedMoment B raw36572step1 raw36572step1Labels := by
      have ha : raw36572step1 = raw36572step0 := by apply Matrix.ext; unfold raw36572step1 raw36572step0; decide +kernel
      have hl : raw36572step0Labels = labelEmbedding1 ∘ raw36572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36572step0 raw36572step0Labels raw36572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

def raw36573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36573step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36573step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36573 raw36573Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw36573 raw36573Labels = mixedMoment B raw36573step0 raw36573step0Labels := by
      have hz : ∀ j, raw36573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36573step0 = (fun i j => raw36573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36573step0 raw36573; decide +kernel
      have hl : raw36573step0Labels = raw36573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36573 raw36573Labels permutation520 hz
    mixedMoment B raw36573step0 raw36573step0Labels = mixedMoment B raw36573step1 raw36573step1Labels := by
      have ha : raw36573step1 = (fun i j => raw36573step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36573step1 raw36573step0; decide +kernel
      have hl : raw36573step1Labels = raw36573step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36573step0 raw36573step0Labels permutation144 permutation7
    mixedMoment B raw36573step1 raw36573step1Labels = mixedMoment B raw36573step2 raw36573step2Labels := by
      have ha : raw36573step2 = raw36573step1 := by apply Matrix.ext; unfold raw36573step2 raw36573step1; decide +kernel
      have hl : raw36573step1Labels = labelEmbedding1 ∘ raw36573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36573step1 raw36573step1Labels raw36573step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw36574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36574step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36574 raw36574Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw36574 raw36574Labels = mixedMoment B raw36574step0 raw36574step0Labels := by
      have ha : raw36574step0 = (fun i j => raw36574 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36574step0 raw36574; decide +kernel
      have hl : raw36574step0Labels = raw36574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36574 raw36574Labels permutation265 permutation3
    mixedMoment B raw36574step0 raw36574step0Labels = mixedMoment B raw36574step1 raw36574step1Labels := by
      have ha : raw36574step1 = raw36574step0 := by apply Matrix.ext; unfold raw36574step1 raw36574step0; decide +kernel
      have hl : raw36574step0Labels = labelEmbedding6 ∘ raw36574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36574step0 raw36574step0Labels raw36574step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw36575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36575step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36575 raw36575Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw36575 raw36575Labels = mixedMoment B raw36575step0 raw36575step0Labels := by
      have ha : raw36575step0 = (fun i j => raw36575 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36575step0 raw36575; decide +kernel
      have hl : raw36575step0Labels = raw36575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36575 raw36575Labels permutation265 permutation3
    mixedMoment B raw36575step0 raw36575step0Labels = mixedMoment B raw36575step1 raw36575step1Labels := by
      have ha : raw36575step1 = raw36575step0 := by apply Matrix.ext; unfold raw36575step1 raw36575step0; decide +kernel
      have hl : raw36575step0Labels = labelEmbedding6 ∘ raw36575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36575step0 raw36575step0Labels raw36575step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw36576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36576step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36576 raw36576Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw36576 raw36576Labels = mixedMoment B raw36576step0 raw36576step0Labels := by
      have ha : raw36576step0 = (fun i j => raw36576 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36576step0 raw36576; decide +kernel
      have hl : raw36576step0Labels = raw36576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36576 raw36576Labels permutation277 permutation3
    mixedMoment B raw36576step0 raw36576step0Labels = mixedMoment B raw36576step1 raw36576step1Labels := by
      have ha : raw36576step1 = raw36576step0 := by apply Matrix.ext; unfold raw36576step1 raw36576step0; decide +kernel
      have hl : raw36576step0Labels = labelEmbedding6 ∘ raw36576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36576step0 raw36576step0Labels raw36576step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw36577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36577step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36577 raw36577Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw36577 raw36577Labels = mixedMoment B raw36577step0 raw36577step0Labels := by
      have ha : raw36577step0 = (fun i j => raw36577 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36577step0 raw36577; decide +kernel
      have hl : raw36577step0Labels = raw36577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36577 raw36577Labels permutation273 permutation3
    mixedMoment B raw36577step0 raw36577step0Labels = mixedMoment B raw36577step1 raw36577step1Labels := by
      have ha : raw36577step1 = raw36577step0 := by apply Matrix.ext; unfold raw36577step1 raw36577step0; decide +kernel
      have hl : raw36577step0Labels = labelEmbedding6 ∘ raw36577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36577step0 raw36577step0Labels raw36577step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

def raw36578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36578step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36578 raw36578Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36578 raw36578Labels = mixedMoment B raw36578step0 raw36578step0Labels := by
      have ha : raw36578step0 = (fun i j => raw36578 (permutation279 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36578step0 raw36578; decide +kernel
      have hl : raw36578step0Labels = raw36578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36578 raw36578Labels permutation279 permutation3
    mixedMoment B raw36578step0 raw36578step0Labels = mixedMoment B raw36578step1 raw36578step1Labels := by
      have ha : raw36578step1 = raw36578step0 := by apply Matrix.ext; unfold raw36578step1 raw36578step0; decide +kernel
      have hl : raw36578step0Labels = labelEmbedding6 ∘ raw36578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36578step0 raw36578step0Labels raw36578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw36579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36579 raw36579Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw36579 raw36579Labels = mixedMoment B raw36579step0 raw36579step0Labels := by
      have ha : raw36579step0 = (fun i j => raw36579 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36579step0 raw36579; decide +kernel
      have hl : raw36579step0Labels = raw36579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36579 raw36579Labels permutation267 permutation3
    mixedMoment B raw36579step0 raw36579step0Labels = mixedMoment B raw36579step1 raw36579step1Labels := by
      have ha : raw36579step1 = raw36579step0 := by apply Matrix.ext; unfold raw36579step1 raw36579step0; decide +kernel
      have hl : raw36579step0Labels = labelEmbedding6 ∘ raw36579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36579step0 raw36579step0Labels raw36579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw36580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36580step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36580 raw36580Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw36580 raw36580Labels = mixedMoment B raw36580step0 raw36580step0Labels := by
      have ha : raw36580step0 = (fun i j => raw36580 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36580step0 raw36580; decide +kernel
      have hl : raw36580step0Labels = raw36580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36580 raw36580Labels permutation267 permutation3
    mixedMoment B raw36580step0 raw36580step0Labels = mixedMoment B raw36580step1 raw36580step1Labels := by
      have ha : raw36580step1 = raw36580step0 := by apply Matrix.ext; unfold raw36580step1 raw36580step0; decide +kernel
      have hl : raw36580step0Labels = labelEmbedding6 ∘ raw36580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36580step0 raw36580step0Labels raw36580step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw36581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36581 raw36581Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36581 raw36581Labels = mixedMoment B raw36581step0 raw36581step0Labels := by
      have ha : raw36581step0 = (fun i j => raw36581 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36581step0 raw36581; decide +kernel
      have hl : raw36581step0Labels = raw36581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36581 raw36581Labels permutation277 permutation3
    mixedMoment B raw36581step0 raw36581step0Labels = mixedMoment B raw36581step1 raw36581step1Labels := by
      have ha : raw36581step1 = raw36581step0 := by apply Matrix.ext; unfold raw36581step1 raw36581step0; decide +kernel
      have hl : raw36581step0Labels = labelEmbedding6 ∘ raw36581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36581step0 raw36581step0Labels raw36581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw36582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36582step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36582 raw36582Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw36582 raw36582Labels = mixedMoment B raw36582step0 raw36582step0Labels := by
      have ha : raw36582step0 = (fun i j => raw36582 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36582step0 raw36582; decide +kernel
      have hl : raw36582step0Labels = raw36582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36582 raw36582Labels permutation265 permutation3
    mixedMoment B raw36582step0 raw36582step0Labels = mixedMoment B raw36582step1 raw36582step1Labels := by
      have ha : raw36582step1 = raw36582step0 := by apply Matrix.ext; unfold raw36582step1 raw36582step0; decide +kernel
      have hl : raw36582step0Labels = labelEmbedding6 ∘ raw36582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36582step0 raw36582step0Labels raw36582step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw36583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36583step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36583 raw36583Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw36583 raw36583Labels = mixedMoment B raw36583step0 raw36583step0Labels := by
      have ha : raw36583step0 = (fun i j => raw36583 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36583step0 raw36583; decide +kernel
      have hl : raw36583step0Labels = raw36583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36583 raw36583Labels permutation265 permutation3
    mixedMoment B raw36583step0 raw36583step0Labels = mixedMoment B raw36583step1 raw36583step1Labels := by
      have ha : raw36583step1 = raw36583step0 := by apply Matrix.ext; unfold raw36583step1 raw36583step0; decide +kernel
      have hl : raw36583step0Labels = labelEmbedding6 ∘ raw36583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36583step0 raw36583step0Labels raw36583step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw36584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36584 raw36584Labels = mixedMoment B node4630 node4630Labels := by
  calc
    mixedMoment B raw36584 raw36584Labels = mixedMoment B raw36584step0 raw36584step0Labels := by
      have ha : raw36584step0 = (fun i j => raw36584 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36584step0 raw36584; decide +kernel
      have hl : raw36584step0Labels = raw36584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36584 raw36584Labels permutation265 permutation3
    mixedMoment B raw36584step0 raw36584step0Labels = mixedMoment B raw36584step1 raw36584step1Labels := by
      have ha : raw36584step1 = raw36584step0 := by apply Matrix.ext; unfold raw36584step1 raw36584step0; decide +kernel
      have hl : raw36584step0Labels = labelEmbedding6 ∘ raw36584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36584step0 raw36584step0Labels raw36584step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4630 node4630Labels := by rfl

def raw36585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36585step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36585step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36585 raw36585Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw36585 raw36585Labels = mixedMoment B raw36585step0 raw36585step0Labels := by
      have ha : raw36585step0 = (fun i j => raw36585 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36585step0 raw36585; decide +kernel
      have hl : raw36585step0Labels = raw36585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36585 raw36585Labels permutation663 permutation3
    mixedMoment B raw36585step0 raw36585step0Labels = mixedMoment B raw36585step1 raw36585step1Labels := by
      have ha : raw36585step1 = -raw36585step0 := by apply Matrix.ext; change ∀ i j, raw36585step1 i j = -(raw36585step0 i j); unfold raw36585step1 raw36585step0; decide +kernel
      have hl : raw36585step1Labels = raw36585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36585step1 raw36585step1Labels = mixedMoment B raw36585step2 raw36585step2Labels := by
      have ha : raw36585step2 = raw36585step1 := by apply Matrix.ext; unfold raw36585step2 raw36585step1; decide +kernel
      have hl : raw36585step1Labels = labelEmbedding6 ∘ raw36585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36585step1 raw36585step1Labels raw36585step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw36586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36586step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36586 raw36586Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw36586 raw36586Labels = mixedMoment B raw36586step0 raw36586step0Labels := by
      have ha : raw36586step0 = (fun i j => raw36586 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36586step0 raw36586; decide +kernel
      have hl : raw36586step0Labels = raw36586Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36586 raw36586Labels permutation657 permutation3
    mixedMoment B raw36586step0 raw36586step0Labels = mixedMoment B raw36586step1 raw36586step1Labels := by
      have ha : raw36586step1 = -raw36586step0 := by apply Matrix.ext; change ∀ i j, raw36586step1 i j = -(raw36586step0 i j); unfold raw36586step1 raw36586step0; decide +kernel
      have hl : raw36586step1Labels = raw36586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36586step1 raw36586step1Labels = mixedMoment B raw36586step2 raw36586step2Labels := by
      have ha : raw36586step2 = raw36586step1 := by apply Matrix.ext; unfold raw36586step2 raw36586step1; decide +kernel
      have hl : raw36586step1Labels = labelEmbedding6 ∘ raw36586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36586step1 raw36586step1Labels raw36586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw36587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36587 raw36587Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw36587 raw36587Labels = mixedMoment B raw36587step0 raw36587step0Labels := by
      have hz : ∀ j, raw36587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36587step0 = (fun i j => raw36587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36587step0 raw36587; decide +kernel
      have hl : raw36587step0Labels = raw36587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36587 raw36587Labels permutation346 hz
    mixedMoment B raw36587step0 raw36587step0Labels = mixedMoment B raw36587step1 raw36587step1Labels := by
      have ha : raw36587step1 = (fun i j => raw36587step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36587step1 raw36587step0; decide +kernel
      have hl : raw36587step1Labels = raw36587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36587step0 raw36587step0Labels permutation58 permutation2
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw36588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36588 raw36588Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw36588 raw36588Labels = mixedMoment B raw36588step0 raw36588step0Labels := by
      have ha : raw36588step0 = (fun i j => raw36588 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36588step0 raw36588; decide +kernel
      have hl : raw36588step0Labels = raw36588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36588 raw36588Labels permutation267 permutation2
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw36589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36589 raw36589Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw36589 raw36589Labels = mixedMoment B raw36589step0 raw36589step0Labels := by
      have hz : ∀ j, raw36589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36589step0 = (fun i j => raw36589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36589step0 raw36589; decide +kernel
      have hl : raw36589step0Labels = raw36589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36589 raw36589Labels permutation346 hz
    mixedMoment B raw36589step0 raw36589step0Labels = mixedMoment B raw36589step1 raw36589step1Labels := by
      have ha : raw36589step1 = (fun i j => raw36589step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36589step1 raw36589step0; decide +kernel
      have hl : raw36589step1Labels = raw36589step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36589step0 raw36589step0Labels permutation56 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw36590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36590 raw36590Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw36590 raw36590Labels = mixedMoment B raw36590step0 raw36590step0Labels := by
      have hz : ∀ j, raw36590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36590step0 = (fun i j => raw36590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36590step0 raw36590; decide +kernel
      have hl : raw36590step0Labels = raw36590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36590 raw36590Labels permutation346 hz
    mixedMoment B raw36590step0 raw36590step0Labels = mixedMoment B raw36590step1 raw36590step1Labels := by
      have ha : raw36590step1 = (fun i j => raw36590step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36590step1 raw36590step0; decide +kernel
      have hl : raw36590step1Labels = raw36590step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36590step0 raw36590step0Labels permutation58 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw36591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36591step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36591step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36591 raw36591Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36591 raw36591Labels = mixedMoment B raw36591step0 raw36591step0Labels := by
      have hz : ∀ j, raw36591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36591step0 = (fun i j => raw36591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36591step0 raw36591; decide +kernel
      have hl : raw36591step0Labels = raw36591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36591 raw36591Labels permutation346 hz
    mixedMoment B raw36591step0 raw36591step0Labels = mixedMoment B raw36591step1 raw36591step1Labels := by
      have ha : raw36591step1 = (fun i j => raw36591step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36591step1 raw36591step0; decide +kernel
      have hl : raw36591step1Labels = raw36591step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36591step0 raw36591step0Labels permutation61 permutation7
    mixedMoment B raw36591step1 raw36591step1Labels = mixedMoment B raw36591step2 raw36591step2Labels := by
      have ha : raw36591step2 = -raw36591step1 := by apply Matrix.ext; change ∀ i j, raw36591step2 i j = -(raw36591step1 i j); unfold raw36591step2 raw36591step1; decide +kernel
      have hl : raw36591step2Labels = raw36591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36591step2 raw36591step2Labels = mixedMoment B raw36591step3 raw36591step3Labels := by
      have ha : raw36591step3 = raw36591step2 := by apply Matrix.ext; unfold raw36591step3 raw36591step2; decide +kernel
      have hl : raw36591step2Labels = labelEmbedding10 ∘ raw36591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36591step2 raw36591step2Labels raw36591step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36592 raw36592Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw36592 raw36592Labels = mixedMoment B raw36592step0 raw36592step0Labels := by
      have hz : ∀ j, raw36592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36592step0 = (fun i j => raw36592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36592step0 raw36592; decide +kernel
      have hl : raw36592step0Labels = raw36592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36592 raw36592Labels permutation346 hz
    mixedMoment B raw36592step0 raw36592step0Labels = mixedMoment B raw36592step1 raw36592step1Labels := by
      have ha : raw36592step1 = (fun i j => raw36592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36592step1 raw36592step0; decide +kernel
      have hl : raw36592step1Labels = raw36592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36592step0 raw36592step0Labels permutation32 permutation3
    mixedMoment B raw36592step1 raw36592step1Labels = mixedMoment B raw36592step2 raw36592step2Labels := by
      have ha : raw36592step2 = raw36592step1 := by apply Matrix.ext; unfold raw36592step2 raw36592step1; decide +kernel
      have hl : raw36592step1Labels = labelEmbedding6 ∘ raw36592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36592step1 raw36592step1Labels raw36592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw36593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36593step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw36593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36593 raw36593Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw36593 raw36593Labels = mixedMoment B raw36593step0 raw36593step0Labels := by
      have ha : raw36593step0 = (fun i j => raw36593 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36593step0 raw36593; decide +kernel
      have hl : raw36593step0Labels = raw36593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36593 raw36593Labels permutation686 permutation3
    mixedMoment B raw36593step0 raw36593step0Labels = mixedMoment B raw36593step1 raw36593step1Labels := by
      have ha : raw36593step1 = -raw36593step0 := by apply Matrix.ext; change ∀ i j, raw36593step1 i j = -(raw36593step0 i j); unfold raw36593step1 raw36593step0; decide +kernel
      have hl : raw36593step1Labels = raw36593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36593step1 raw36593step1Labels = mixedMoment B raw36593step2 raw36593step2Labels := by
      have ha : raw36593step2 = raw36593step1 := by apply Matrix.ext; unfold raw36593step2 raw36593step1; decide +kernel
      have hl : raw36593step1Labels = labelEmbedding6 ∘ raw36593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36593step1 raw36593step1Labels raw36593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw36594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw36594step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw36594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36594step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw36594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36594 raw36594Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw36594 raw36594Labels = mixedMoment B raw36594step0 raw36594step0Labels := by
      have hz : ∀ j, raw36594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36594step0 = (fun i j => raw36594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36594step0 raw36594; decide +kernel
      have hl : raw36594step0Labels = raw36594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36594 raw36594Labels permutation346 hz
    mixedMoment B raw36594step0 raw36594step0Labels = mixedMoment B raw36594step1 raw36594step1Labels := by
      have ha : raw36594step1 = (fun i j => raw36594step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36594step1 raw36594step0; decide +kernel
      have hl : raw36594step1Labels = raw36594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36594step0 raw36594step0Labels permutation151 permutation3
    mixedMoment B raw36594step1 raw36594step1Labels = mixedMoment B raw36594step2 raw36594step2Labels := by
      have ha : raw36594step2 = -raw36594step1 := by apply Matrix.ext; change ∀ i j, raw36594step2 i j = -(raw36594step1 i j); unfold raw36594step2 raw36594step1; decide +kernel
      have hl : raw36594step2Labels = raw36594step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36594step2 raw36594step2Labels = mixedMoment B raw36594step3 raw36594step3Labels := by
      have ha : raw36594step3 = raw36594step2 := by apply Matrix.ext; unfold raw36594step3 raw36594step2; decide +kernel
      have hl : raw36594step2Labels = labelEmbedding6 ∘ raw36594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36594step2 raw36594step2Labels raw36594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw36595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw36595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36595 raw36595Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw36595 raw36595Labels = mixedMoment B raw36595step0 raw36595step0Labels := by
      have hz : ∀ j, raw36595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36595step0 = (fun i j => raw36595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36595step0 raw36595; decide +kernel
      have hl : raw36595step0Labels = raw36595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36595 raw36595Labels permutation346 hz
    mixedMoment B raw36595step0 raw36595step0Labels = mixedMoment B raw36595step1 raw36595step1Labels := by
      have ha : raw36595step1 = (fun i j => raw36595step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36595step1 raw36595step0; decide +kernel
      have hl : raw36595step1Labels = raw36595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36595step0 raw36595step0Labels permutation145 permutation3
    mixedMoment B raw36595step1 raw36595step1Labels = mixedMoment B raw36595step2 raw36595step2Labels := by
      have ha : raw36595step2 = -raw36595step1 := by apply Matrix.ext; change ∀ i j, raw36595step2 i j = -(raw36595step1 i j); unfold raw36595step2 raw36595step1; decide +kernel
      have hl : raw36595step2Labels = raw36595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36595step2 raw36595step2Labels = mixedMoment B raw36595step3 raw36595step3Labels := by
      have ha : raw36595step3 = raw36595step2 := by apply Matrix.ext; unfold raw36595step3 raw36595step2; decide +kernel
      have hl : raw36595step2Labels = labelEmbedding6 ∘ raw36595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36595step2 raw36595step2Labels raw36595step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw36596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36596step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36596step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36596step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36596 raw36596Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw36596 raw36596Labels = mixedMoment B raw36596step0 raw36596step0Labels := by
      have hz : ∀ j, raw36596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36596step0 = (fun i j => raw36596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36596step0 raw36596; decide +kernel
      have hl : raw36596step0Labels = raw36596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36596 raw36596Labels permutation346 hz
    mixedMoment B raw36596step0 raw36596step0Labels = mixedMoment B raw36596step1 raw36596step1Labels := by
      have ha : raw36596step1 = (fun i j => raw36596step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36596step1 raw36596step0; decide +kernel
      have hl : raw36596step1Labels = raw36596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36596step0 raw36596step0Labels permutation61 permutation7
    mixedMoment B raw36596step1 raw36596step1Labels = mixedMoment B raw36596step2 raw36596step2Labels := by
      have ha : raw36596step2 = -raw36596step1 := by apply Matrix.ext; change ∀ i j, raw36596step2 i j = -(raw36596step1 i j); unfold raw36596step2 raw36596step1; decide +kernel
      have hl : raw36596step2Labels = raw36596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36596step2 raw36596step2Labels = mixedMoment B raw36596step3 raw36596step3Labels := by
      have ha : raw36596step3 = raw36596step2 := by apply Matrix.ext; unfold raw36596step3 raw36596step2; decide +kernel
      have hl : raw36596step2Labels = labelEmbedding10 ∘ raw36596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36596step2 raw36596step2Labels raw36596step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw36597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36597 raw36597Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw36597 raw36597Labels = mixedMoment B raw36597step0 raw36597step0Labels := by
      have ha : raw36597step0 = (fun i j => raw36597 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36597step0 raw36597; decide +kernel
      have hl : raw36597step0Labels = raw36597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36597 raw36597Labels permutation160 permutation3
    mixedMoment B raw36597step0 raw36597step0Labels = mixedMoment B raw36597step1 raw36597step1Labels := by
      have ha : raw36597step1 = raw36597step0 := by apply Matrix.ext; unfold raw36597step1 raw36597step0; decide +kernel
      have hl : raw36597step0Labels = labelEmbedding6 ∘ raw36597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36597step0 raw36597step0Labels raw36597step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw36598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36598 raw36598Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw36598 raw36598Labels = mixedMoment B raw36598step0 raw36598step0Labels := by
      have ha : raw36598step0 = (fun i j => raw36598 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36598step0 raw36598; decide +kernel
      have hl : raw36598step0Labels = raw36598Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36598 raw36598Labels permutation267 permutation2
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw36599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36599 raw36599Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw36599 raw36599Labels = mixedMoment B raw36599step0 raw36599step0Labels := by
      have ha : raw36599step0 = (fun i j => raw36599 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36599step0 raw36599; decide +kernel
      have hl : raw36599step0Labels = raw36599Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36599 raw36599Labels permutation271 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw36600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36600 raw36600Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36600 raw36600Labels = mixedMoment B raw36600step0 raw36600step0Labels := by
      have ha : raw36600step0 = (fun i j => raw36600 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36600step0 raw36600; decide +kernel
      have hl : raw36600step0Labels = raw36600Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36600 raw36600Labels permutation277 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36601 raw36601Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36601 raw36601Labels = mixedMoment B raw36601step0 raw36601step0Labels := by
      have ha : raw36601step0 = (fun i j => raw36601 (permutation270 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36601step0 raw36601; decide +kernel
      have hl : raw36601step0Labels = raw36601Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36601 raw36601Labels permutation270 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36602 raw36602Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw36602 raw36602Labels = mixedMoment B raw36602step0 raw36602step0Labels := by
      have hz : ∀ j, raw36602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36602step0 = (fun i j => raw36602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36602step0 raw36602; decide +kernel
      have hl : raw36602step0Labels = raw36602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36602 raw36602Labels permutation346 hz
    mixedMoment B raw36602step0 raw36602step0Labels = mixedMoment B raw36602step1 raw36602step1Labels := by
      have ha : raw36602step1 = (fun i j => raw36602step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36602step1 raw36602step0; decide +kernel
      have hl : raw36602step1Labels = raw36602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36602step0 raw36602step0Labels permutation34 permutation3
    mixedMoment B raw36602step1 raw36602step1Labels = mixedMoment B raw36602step2 raw36602step2Labels := by
      have ha : raw36602step2 = raw36602step1 := by apply Matrix.ext; unfold raw36602step2 raw36602step1; decide +kernel
      have hl : raw36602step1Labels = labelEmbedding6 ∘ raw36602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36602step1 raw36602step1Labels raw36602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw36603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36603 raw36603Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36603 raw36603Labels = mixedMoment B raw36603step0 raw36603step0Labels := by
      have hz : ∀ j, raw36603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36603step0 = (fun i j => raw36603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36603step0 raw36603; decide +kernel
      have hl : raw36603step0Labels = raw36603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36603 raw36603Labels permutation346 hz
    mixedMoment B raw36603step0 raw36603step0Labels = mixedMoment B raw36603step1 raw36603step1Labels := by
      have ha : raw36603step1 = (fun i j => raw36603step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36603step1 raw36603step0; decide +kernel
      have hl : raw36603step1Labels = raw36603step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36603step0 raw36603step0Labels permutation59 permutation2
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw36604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw36604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36604 raw36604Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw36604 raw36604Labels = mixedMoment B raw36604step0 raw36604step0Labels := by
      have ha : raw36604step0 = (fun i j => raw36604 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36604step0 raw36604; decide +kernel
      have hl : raw36604step0Labels = raw36604Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36604 raw36604Labels permutation268 permutation2
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw36605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw36605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36605 raw36605Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36605 raw36605Labels = mixedMoment B raw36605step0 raw36605step0Labels := by
      have hz : ∀ j, raw36605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36605step0 = (fun i j => raw36605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36605step0 raw36605; decide +kernel
      have hl : raw36605step0Labels = raw36605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36605 raw36605Labels permutation346 hz
    mixedMoment B raw36605step0 raw36605step0Labels = mixedMoment B raw36605step1 raw36605step1Labels := by
      have ha : raw36605step1 = (fun i j => raw36605step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36605step1 raw36605step0; decide +kernel
      have hl : raw36605step1Labels = raw36605step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36605step0 raw36605step0Labels permutation59 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw36606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw36606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36606 raw36606Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36606 raw36606Labels = mixedMoment B raw36606step0 raw36606step0Labels := by
      have hz : ∀ j, raw36606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36606step0 = (fun i j => raw36606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36606step0 raw36606; decide +kernel
      have hl : raw36606step0Labels = raw36606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36606 raw36606Labels permutation346 hz
    mixedMoment B raw36606step0 raw36606step0Labels = mixedMoment B raw36606step1 raw36606step1Labels := by
      have ha : raw36606step1 = (fun i j => raw36606step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36606step1 raw36606step0; decide +kernel
      have hl : raw36606step1Labels = raw36606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36606step0 raw36606step0Labels permutation61 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw36607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36607 raw36607Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw36607 raw36607Labels = mixedMoment B raw36607step0 raw36607step0Labels := by
      have hz : ∀ j, raw36607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36607step0 = (fun i j => raw36607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36607step0 raw36607; decide +kernel
      have hl : raw36607step0Labels = raw36607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36607 raw36607Labels permutation346 hz
    mixedMoment B raw36607step0 raw36607step0Labels = mixedMoment B raw36607step1 raw36607step1Labels := by
      have ha : raw36607step1 = (fun i j => raw36607step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36607step1 raw36607step0; decide +kernel
      have hl : raw36607step1Labels = raw36607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36607step0 raw36607step0Labels permutation32 permutation3
    mixedMoment B raw36607step1 raw36607step1Labels = mixedMoment B raw36607step2 raw36607step2Labels := by
      have ha : raw36607step2 = raw36607step1 := by apply Matrix.ext; unfold raw36607step2 raw36607step1; decide +kernel
      have hl : raw36607step1Labels = labelEmbedding6 ∘ raw36607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36607step1 raw36607step1Labels raw36607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4966 node4966Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
