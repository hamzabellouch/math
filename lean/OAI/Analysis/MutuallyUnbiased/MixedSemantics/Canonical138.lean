import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17664 raw17664Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17664 raw17664Labels = mixedMoment B raw17664step0 raw17664step0Labels := by
      have hz : ∀ j, raw17664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17664step0 = (fun i j => raw17664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17664step0 raw17664; decide +kernel
      have hl : raw17664step0Labels = raw17664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17664 raw17664Labels permutation434 hz
    mixedMoment B raw17664step0 raw17664step0Labels = mixedMoment B raw17664step1 raw17664step1Labels := by
      have ha : raw17664step1 = (fun i j => raw17664step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17664step1 raw17664step0; decide +kernel
      have hl : raw17664step1Labels = raw17664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17664step0 raw17664step0Labels permutation150 permutation2
    mixedMoment B raw17664step1 raw17664step1Labels = mixedMoment B raw17664step2 raw17664step2Labels := by
      have ha : raw17664step2 = -raw17664step1 := by apply Matrix.ext; change ∀ i j, raw17664step2 i j = -(raw17664step1 i j); unfold raw17664step2 raw17664step1; decide +kernel
      have hl : raw17664step2Labels = raw17664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17665 raw17665Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17665 raw17665Labels = mixedMoment B raw17665step0 raw17665step0Labels := by
      have hz : ∀ j, raw17665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17665step0 = (fun i j => raw17665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17665step0 raw17665; decide +kernel
      have hl : raw17665step0Labels = raw17665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17665 raw17665Labels permutation346 hz
    mixedMoment B raw17665step0 raw17665step0Labels = mixedMoment B raw17665step1 raw17665step1Labels := by
      have ha : raw17665step1 = (fun i j => raw17665step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17665step1 raw17665step0; decide +kernel
      have hl : raw17665step1Labels = raw17665step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17665step0 raw17665step0Labels permutation150 permutation2
    mixedMoment B raw17665step1 raw17665step1Labels = mixedMoment B raw17665step2 raw17665step2Labels := by
      have ha : raw17665step2 = -raw17665step1 := by apply Matrix.ext; change ∀ i j, raw17665step2 i j = -(raw17665step1 i j); unfold raw17665step2 raw17665step1; decide +kernel
      have hl : raw17665step2Labels = raw17665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17666step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17666step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw17666step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17666 raw17666Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw17666 raw17666Labels = mixedMoment B raw17666step0 raw17666step0Labels := by
      have hz : ∀ j, raw17666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17666step0 = (fun i j => raw17666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17666step0 raw17666; decide +kernel
      have hl : raw17666step0Labels = raw17666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17666 raw17666Labels permutation434 hz
    mixedMoment B raw17666step0 raw17666step0Labels = mixedMoment B raw17666step1 raw17666step1Labels := by
      have hz : ∀ j, raw17666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17666step1 = (fun i j => raw17666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17666step1 raw17666step0; decide +kernel
      have hl : raw17666step1Labels = raw17666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17666step0 raw17666step0Labels permutation80 hz
    mixedMoment B raw17666step1 raw17666step1Labels = mixedMoment B raw17666step2 raw17666step2Labels := by
      have hz : ∀ i, raw17666step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw17666step2 = (fun i j => raw17666step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw17666step2 raw17666step1; decide +kernel
      have hl : raw17666step2Labels = (fun j => raw17666step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw17666step1 raw17666step1Labels permutation4 hz
    mixedMoment B raw17666step2 raw17666step2Labels = mixedMoment B raw17666step3 raw17666step3Labels := by
      have ha : raw17666step3 = raw17666step2 := by apply Matrix.ext; unfold raw17666step3 raw17666step2; decide +kernel
      have hl : raw17666step2Labels = labelEmbedding2 ∘ raw17666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17666step2 raw17666step2Labels raw17666step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw17667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17667 raw17667Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17667 raw17667Labels = mixedMoment B raw17667step0 raw17667step0Labels := by
      have hz : ∀ j, raw17667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17667step0 = (fun i j => raw17667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17667step0 raw17667; decide +kernel
      have hl : raw17667step0Labels = raw17667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17667 raw17667Labels permutation434 hz
    mixedMoment B raw17667step0 raw17667step0Labels = mixedMoment B raw17667step1 raw17667step1Labels := by
      have ha : raw17667step1 = (fun i j => raw17667step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17667step1 raw17667step0; decide +kernel
      have hl : raw17667step1Labels = raw17667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17667step0 raw17667step0Labels permutation34 permutation3
    mixedMoment B raw17667step1 raw17667step1Labels = mixedMoment B raw17667step2 raw17667step2Labels := by
      have ha : raw17667step2 = raw17667step1 := by apply Matrix.ext; unfold raw17667step2 raw17667step1; decide +kernel
      have hl : raw17667step1Labels = labelEmbedding6 ∘ raw17667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17667step1 raw17667step1Labels raw17667step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17668 raw17668Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17668 raw17668Labels = mixedMoment B raw17668step0 raw17668step0Labels := by
      have hz : ∀ j, raw17668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17668step0 = (fun i j => raw17668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17668step0 raw17668; decide +kernel
      have hl : raw17668step0Labels = raw17668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17668 raw17668Labels permutation434 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw17669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17669 raw17669Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw17669 raw17669Labels = mixedMoment B raw17669step0 raw17669step0Labels := by
      have ha : raw17669step0 = (fun i j => raw17669 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17669step0 raw17669; decide +kernel
      have hl : raw17669step0Labels = raw17669Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17669 raw17669Labels permutation158 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw17670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17670 raw17670Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17670 raw17670Labels = mixedMoment B raw17670step0 raw17670step0Labels := by
      have hz : ∀ j, raw17670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17670step0 = (fun i j => raw17670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17670step0 raw17670; decide +kernel
      have hl : raw17670step0Labels = raw17670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17670 raw17670Labels permutation434 hz
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17671 raw17671Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17671 raw17671Labels = mixedMoment B raw17671step0 raw17671step0Labels := by
      have hz : ∀ j, raw17671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17671step0 = (fun i j => raw17671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17671step0 raw17671; decide +kernel
      have hl : raw17671step0Labels = raw17671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17671 raw17671Labels permutation346 hz
    mixedMoment B raw17671step0 raw17671step0Labels = mixedMoment B raw17671step1 raw17671step1Labels := by
      have ha : raw17671step1 = (fun i j => raw17671step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17671step1 raw17671step0; decide +kernel
      have hl : raw17671step1Labels = raw17671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17671step0 raw17671step0Labels permutation34 permutation3
    mixedMoment B raw17671step1 raw17671step1Labels = mixedMoment B raw17671step2 raw17671step2Labels := by
      have ha : raw17671step2 = raw17671step1 := by apply Matrix.ext; unfold raw17671step2 raw17671step1; decide +kernel
      have hl : raw17671step1Labels = labelEmbedding6 ∘ raw17671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17671step1 raw17671step1Labels raw17671step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17672 raw17672Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17672 raw17672Labels = mixedMoment B raw17672step0 raw17672step0Labels := by
      have hz : ∀ j, raw17672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17672step0 = (fun i j => raw17672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17672step0 raw17672; decide +kernel
      have hl : raw17672step0Labels = raw17672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17672 raw17672Labels permutation346 hz
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw17673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17673 raw17673Labels = mixedMoment B node5476 node5476Labels := by
  calc
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw17674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17674 raw17674Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17674 raw17674Labels = mixedMoment B raw17674step0 raw17674step0Labels := by
      have hz : ∀ j, raw17674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17674step0 = (fun i j => raw17674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17674step0 raw17674; decide +kernel
      have hl : raw17674step0Labels = raw17674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17674 raw17674Labels permutation346 hz
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17675step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17675 raw17675Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17675 raw17675Labels = mixedMoment B raw17675step0 raw17675step0Labels := by
      have hz : ∀ j, raw17675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17675step0 = (fun i j => raw17675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17675step0 raw17675; decide +kernel
      have hl : raw17675step0Labels = raw17675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675 raw17675Labels permutation434 hz
    mixedMoment B raw17675step0 raw17675step0Labels = mixedMoment B raw17675step1 raw17675step1Labels := by
      have hz : ∀ j, raw17675step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17675step1 = (fun i j => raw17675step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17675step1 raw17675step0; decide +kernel
      have hl : raw17675step1Labels = raw17675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17675step0 raw17675step0Labels permutation80 hz
    mixedMoment B raw17675step1 raw17675step1Labels = mixedMoment B raw17675step2 raw17675step2Labels := by
      have ha : raw17675step2 = (fun i j => raw17675step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17675step2 raw17675step1; decide +kernel
      have hl : raw17675step2Labels = raw17675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17675step1 raw17675step1Labels permutation8 permutation3
    mixedMoment B raw17675step2 raw17675step2Labels = mixedMoment B raw17675step3 raw17675step3Labels := by
      have ha : raw17675step3 = raw17675step2 := by apply Matrix.ext; unfold raw17675step3 raw17675step2; decide +kernel
      have hl : raw17675step2Labels = labelEmbedding6 ∘ raw17675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17675step2 raw17675step2Labels raw17675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw17676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17676 raw17676Labels = mixedMoment B node5466 node5466Labels := by
  calc
    mixedMoment B raw17676 raw17676Labels = mixedMoment B raw17676step0 raw17676step0Labels := by
      have hz : ∀ j, raw17676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17676step0 = (fun i j => raw17676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17676step0 raw17676; decide +kernel
      have hl : raw17676step0Labels = raw17676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17676 raw17676Labels permutation434 hz
    mixedMoment B raw17676step0 raw17676step0Labels = mixedMoment B raw17676step1 raw17676step1Labels := by
      have hz : ∀ j, raw17676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17676step1 = (fun i j => raw17676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17676step1 raw17676step0; decide +kernel
      have hl : raw17676step1Labels = raw17676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17676step0 raw17676step0Labels permutation80 hz
    _ = mixedMoment B node5466 node5466Labels := by rfl

def raw17677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17677 raw17677Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17677 raw17677Labels = mixedMoment B raw17677step0 raw17677step0Labels := by
      have hz : ∀ j, raw17677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17677step0 = (fun i j => raw17677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17677step0 raw17677; decide +kernel
      have hl : raw17677step0Labels = raw17677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17677 raw17677Labels permutation434 hz
    mixedMoment B raw17677step0 raw17677step0Labels = mixedMoment B raw17677step1 raw17677step1Labels := by
      have ha : raw17677step1 = (fun i j => raw17677step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17677step1 raw17677step0; decide +kernel
      have hl : raw17677step1Labels = raw17677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17677step0 raw17677step0Labels permutation127 permutation2
    mixedMoment B raw17677step1 raw17677step1Labels = mixedMoment B raw17677step2 raw17677step2Labels := by
      have ha : raw17677step2 = -raw17677step1 := by apply Matrix.ext; change ∀ i j, raw17677step2 i j = -(raw17677step1 i j); unfold raw17677step2 raw17677step1; decide +kernel
      have hl : raw17677step2Labels = raw17677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw17678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17678 raw17678Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw17678 raw17678Labels = mixedMoment B raw17678step0 raw17678step0Labels := by
      have hz : ∀ j, raw17678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17678step0 = (fun i j => raw17678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17678step0 raw17678; decide +kernel
      have hl : raw17678step0Labels = raw17678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17678 raw17678Labels permutation346 hz
    mixedMoment B raw17678step0 raw17678step0Labels = mixedMoment B raw17678step1 raw17678step1Labels := by
      have ha : raw17678step1 = (fun i j => raw17678step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17678step1 raw17678step0; decide +kernel
      have hl : raw17678step1Labels = raw17678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17678step0 raw17678step0Labels permutation127 permutation2
    mixedMoment B raw17678step1 raw17678step1Labels = mixedMoment B raw17678step2 raw17678step2Labels := by
      have ha : raw17678step2 = -raw17678step1 := by apply Matrix.ext; change ∀ i j, raw17678step2 i j = -(raw17678step1 i j); unfold raw17678step2 raw17678step1; decide +kernel
      have hl : raw17678step2Labels = raw17678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw17679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw17679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw17679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17679 raw17679Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17679 raw17679Labels = mixedMoment B raw17679step0 raw17679step0Labels := by
      have hz : ∀ j, raw17679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17679step0 = (fun i j => raw17679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17679step0 raw17679; decide +kernel
      have hl : raw17679step0Labels = raw17679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17679 raw17679Labels permutation434 hz
    mixedMoment B raw17679step0 raw17679step0Labels = mixedMoment B raw17679step1 raw17679step1Labels := by
      have hz : ∀ j, raw17679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17679step1 = (fun i j => raw17679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17679step1 raw17679step0; decide +kernel
      have hl : raw17679step1Labels = raw17679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17679step0 raw17679step0Labels permutation80 hz
    mixedMoment B raw17679step1 raw17679step1Labels = mixedMoment B raw17679step2 raw17679step2Labels := by
      have ha : raw17679step2 = (fun i j => raw17679step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17679step2 raw17679step1; decide +kernel
      have hl : raw17679step2Labels = raw17679step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17679step1 raw17679step1Labels permutation9 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw17680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw17680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17680step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17680step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17680step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17680 raw17680Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17680 raw17680Labels = mixedMoment B raw17680step0 raw17680step0Labels := by
      have hz : ∀ j, raw17680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17680step0 = (fun i j => raw17680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17680step0 raw17680; decide +kernel
      have hl : raw17680step0Labels = raw17680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17680 raw17680Labels permutation434 hz
    mixedMoment B raw17680step0 raw17680step0Labels = mixedMoment B raw17680step1 raw17680step1Labels := by
      have hz : ∀ j, raw17680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17680step1 = (fun i j => raw17680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17680step1 raw17680step0; decide +kernel
      have hl : raw17680step1Labels = raw17680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17680step0 raw17680step0Labels permutation80 hz
    mixedMoment B raw17680step1 raw17680step1Labels = mixedMoment B raw17680step2 raw17680step2Labels := by
      have ha : raw17680step2 = (fun i j => raw17680step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17680step2 raw17680step1; decide +kernel
      have hl : raw17680step2Labels = raw17680step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17680step1 raw17680step1Labels permutation30 permutation3
    mixedMoment B raw17680step2 raw17680step2Labels = mixedMoment B raw17680step3 raw17680step3Labels := by
      have ha : raw17680step3 = -raw17680step2 := by apply Matrix.ext; change ∀ i j, raw17680step3 i j = -(raw17680step2 i j); unfold raw17680step3 raw17680step2; decide +kernel
      have hl : raw17680step3Labels = raw17680step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17680step3 raw17680step3Labels = mixedMoment B raw17680step4 raw17680step4Labels := by
      have ha : raw17680step4 = raw17680step3 := by apply Matrix.ext; unfold raw17680step4 raw17680step3; decide +kernel
      have hl : raw17680step3Labels = labelEmbedding6 ∘ raw17680step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17680step3 raw17680step3Labels raw17680step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw17681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17681 raw17681Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17681 raw17681Labels = mixedMoment B raw17681step0 raw17681step0Labels := by
      have hz : ∀ j, raw17681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17681step0 = (fun i j => raw17681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17681step0 raw17681; decide +kernel
      have hl : raw17681step0Labels = raw17681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17681 raw17681Labels permutation434 hz
    mixedMoment B raw17681step0 raw17681step0Labels = mixedMoment B raw17681step1 raw17681step1Labels := by
      have ha : raw17681step1 = (fun i j => raw17681step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17681step1 raw17681step0; decide +kernel
      have hl : raw17681step1Labels = raw17681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17681step0 raw17681step0Labels permutation149 permutation3
    mixedMoment B raw17681step1 raw17681step1Labels = mixedMoment B raw17681step2 raw17681step2Labels := by
      have ha : raw17681step2 = -raw17681step1 := by apply Matrix.ext; change ∀ i j, raw17681step2 i j = -(raw17681step1 i j); unfold raw17681step2 raw17681step1; decide +kernel
      have hl : raw17681step2Labels = raw17681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17681step2 raw17681step2Labels = mixedMoment B raw17681step3 raw17681step3Labels := by
      have ha : raw17681step3 = raw17681step2 := by apply Matrix.ext; unfold raw17681step3 raw17681step2; decide +kernel
      have hl : raw17681step2Labels = labelEmbedding6 ∘ raw17681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17681step2 raw17681step2Labels raw17681step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17682step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17682 raw17682Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17682 raw17682Labels = mixedMoment B raw17682step0 raw17682step0Labels := by
      have hz : ∀ j, raw17682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17682step0 = (fun i j => raw17682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17682step0 raw17682; decide +kernel
      have hl : raw17682step0Labels = raw17682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17682 raw17682Labels permutation346 hz
    mixedMoment B raw17682step0 raw17682step0Labels = mixedMoment B raw17682step1 raw17682step1Labels := by
      have ha : raw17682step1 = (fun i j => raw17682step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17682step1 raw17682step0; decide +kernel
      have hl : raw17682step1Labels = raw17682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17682step0 raw17682step0Labels permutation149 permutation3
    mixedMoment B raw17682step1 raw17682step1Labels = mixedMoment B raw17682step2 raw17682step2Labels := by
      have ha : raw17682step2 = -raw17682step1 := by apply Matrix.ext; change ∀ i j, raw17682step2 i j = -(raw17682step1 i j); unfold raw17682step2 raw17682step1; decide +kernel
      have hl : raw17682step2Labels = raw17682step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17682step2 raw17682step2Labels = mixedMoment B raw17682step3 raw17682step3Labels := by
      have ha : raw17682step3 = raw17682step2 := by apply Matrix.ext; unfold raw17682step3 raw17682step2; decide +kernel
      have hl : raw17682step2Labels = labelEmbedding6 ∘ raw17682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17682step2 raw17682step2Labels raw17682step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17683 raw17683Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17683 raw17683Labels = mixedMoment B raw17683step0 raw17683step0Labels := by
      have hz : ∀ j, raw17683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17683step0 = (fun i j => raw17683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17683step0 raw17683; decide +kernel
      have hl : raw17683step0Labels = raw17683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17683 raw17683Labels permutation434 hz
    mixedMoment B raw17683step0 raw17683step0Labels = mixedMoment B raw17683step1 raw17683step1Labels := by
      have hz : ∀ j, raw17683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17683step1 = (fun i j => raw17683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17683step1 raw17683step0; decide +kernel
      have hl : raw17683step1Labels = raw17683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17683step0 raw17683step0Labels permutation80 hz
    mixedMoment B raw17683step1 raw17683step1Labels = mixedMoment B raw17683step2 raw17683step2Labels := by
      have ha : raw17683step2 = (fun i j => raw17683step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17683step2 raw17683step1; decide +kernel
      have hl : raw17683step2Labels = raw17683step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17683step1 raw17683step1Labels permutation30 permutation2
    mixedMoment B raw17683step2 raw17683step2Labels = mixedMoment B raw17683step3 raw17683step3Labels := by
      have ha : raw17683step3 = -raw17683step2 := by apply Matrix.ext; change ∀ i j, raw17683step3 i j = -(raw17683step2 i j); unfold raw17683step3 raw17683step2; decide +kernel
      have hl : raw17683step3Labels = raw17683step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17684 raw17684Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw17684 raw17684Labels = mixedMoment B raw17684step0 raw17684step0Labels := by
      have hz : ∀ j, raw17684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17684step0 = (fun i j => raw17684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17684step0 raw17684; decide +kernel
      have hl : raw17684step0Labels = raw17684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17684 raw17684Labels permutation434 hz
    mixedMoment B raw17684step0 raw17684step0Labels = mixedMoment B raw17684step1 raw17684step1Labels := by
      have ha : raw17684step1 = (fun i j => raw17684step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17684step1 raw17684step0; decide +kernel
      have hl : raw17684step1Labels = raw17684step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17684step0 raw17684step0Labels permutation150 permutation2
    mixedMoment B raw17684step1 raw17684step1Labels = mixedMoment B raw17684step2 raw17684step2Labels := by
      have ha : raw17684step2 = -raw17684step1 := by apply Matrix.ext; change ∀ i j, raw17684step2 i j = -(raw17684step1 i j); unfold raw17684step2 raw17684step1; decide +kernel
      have hl : raw17684step2Labels = raw17684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw17685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17685 raw17685Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw17685 raw17685Labels = mixedMoment B raw17685step0 raw17685step0Labels := by
      have hz : ∀ j, raw17685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17685step0 = (fun i j => raw17685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17685step0 raw17685; decide +kernel
      have hl : raw17685step0Labels = raw17685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17685 raw17685Labels permutation346 hz
    mixedMoment B raw17685step0 raw17685step0Labels = mixedMoment B raw17685step1 raw17685step1Labels := by
      have ha : raw17685step1 = (fun i j => raw17685step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17685step1 raw17685step0; decide +kernel
      have hl : raw17685step1Labels = raw17685step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17685step0 raw17685step0Labels permutation150 permutation2
    mixedMoment B raw17685step1 raw17685step1Labels = mixedMoment B raw17685step2 raw17685step2Labels := by
      have ha : raw17685step2 = -raw17685step1 := by apply Matrix.ext; change ∀ i j, raw17685step2 i j = -(raw17685step1 i j); unfold raw17685step2 raw17685step1; decide +kernel
      have hl : raw17685step2Labels = raw17685step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw17686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]
def raw17686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17686step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw17686step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw17686step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17686step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw17686step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17686 raw17686Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw17686 raw17686Labels = mixedMoment B raw17686step0 raw17686step0Labels := by
      have hz : ∀ j, raw17686 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17686step0 = (fun i j => raw17686 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17686step0 raw17686; decide +kernel
      have hl : raw17686step0Labels = raw17686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17686 raw17686Labels permutation520 hz
    mixedMoment B raw17686step0 raw17686step0Labels = mixedMoment B raw17686step1 raw17686step1Labels := by
      have hz : ∀ j, raw17686step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17686step1 = (fun i j => raw17686step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17686step1 raw17686step0; decide +kernel
      have hl : raw17686step1Labels = raw17686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17686step0 raw17686step0Labels permutation104 hz
    mixedMoment B raw17686step1 raw17686step1Labels = mixedMoment B raw17686step2 raw17686step2Labels := by
      have hz : ∀ j, raw17686step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw17686step2 = (fun i j => raw17686step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw17686step2 raw17686step1; decide +kernel
      have hl : raw17686step2Labels = raw17686step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17686step1 raw17686step1Labels permutation20 hz
    mixedMoment B raw17686step2 raw17686step2Labels = mixedMoment B raw17686step3 raw17686step3Labels := by
      have hz : ∀ i, raw17686step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw17686step3 = (fun i j => raw17686step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw17686step3 raw17686step2; decide +kernel
      have hl : raw17686step3Labels = (fun j => raw17686step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw17686step2 raw17686step2Labels permutation4 hz
    mixedMoment B raw17686step3 raw17686step3Labels = mixedMoment B raw17686step4 raw17686step4Labels := by
      have ha : raw17686step4 = (fun i j => raw17686step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17686step4 raw17686step3; decide +kernel
      have hl : raw17686step4Labels = raw17686step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17686step3 raw17686step3Labels permutation6 permutation0
    mixedMoment B raw17686step4 raw17686step4Labels = mixedMoment B raw17686step5 raw17686step5Labels := by
      have ha : raw17686step5 = -raw17686step4 := by apply Matrix.ext; change ∀ i j, raw17686step5 i j = -(raw17686step4 i j); unfold raw17686step5 raw17686step4; decide +kernel
      have hl : raw17686step5Labels = raw17686step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17686step5 raw17686step5Labels = mixedMoment B raw17686step6 raw17686step6Labels := by
      have ha : raw17686step6 = raw17686step5 := by apply Matrix.ext; unfold raw17686step6 raw17686step5; decide +kernel
      have hl : raw17686step5Labels = labelEmbedding2 ∘ raw17686step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17686step5 raw17686step5Labels raw17686step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw17687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17687 raw17687Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw17687 raw17687Labels = mixedMoment B raw17687step0 raw17687step0Labels := by
      have hz : ∀ j, raw17687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17687step0 = (fun i j => raw17687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17687step0 raw17687; decide +kernel
      have hl : raw17687step0Labels = raw17687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17687 raw17687Labels permutation434 hz
    mixedMoment B raw17687step0 raw17687step0Labels = mixedMoment B raw17687step1 raw17687step1Labels := by
      have ha : raw17687step1 = (fun i j => raw17687step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17687step1 raw17687step0; decide +kernel
      have hl : raw17687step1Labels = raw17687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17687step0 raw17687step0Labels permutation32 permutation3
    mixedMoment B raw17687step1 raw17687step1Labels = mixedMoment B raw17687step2 raw17687step2Labels := by
      have ha : raw17687step2 = raw17687step1 := by apply Matrix.ext; unfold raw17687step2 raw17687step1; decide +kernel
      have hl : raw17687step1Labels = labelEmbedding6 ∘ raw17687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17687step1 raw17687step1Labels raw17687step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw17688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17688 raw17688Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw17688 raw17688Labels = mixedMoment B raw17688step0 raw17688step0Labels := by
      have hz : ∀ j, raw17688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17688step0 = (fun i j => raw17688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17688step0 raw17688; decide +kernel
      have hl : raw17688step0Labels = raw17688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17688 raw17688Labels permutation434 hz
    mixedMoment B raw17688step0 raw17688step0Labels = mixedMoment B raw17688step1 raw17688step1Labels := by
      have ha : raw17688step1 = (fun i j => raw17688step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17688step1 raw17688step0; decide +kernel
      have hl : raw17688step1Labels = raw17688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17688step0 raw17688step0Labels permutation144 permutation2
    mixedMoment B raw17688step1 raw17688step1Labels = mixedMoment B raw17688step2 raw17688step2Labels := by
      have ha : raw17688step2 = -raw17688step1 := by apply Matrix.ext; change ∀ i j, raw17688step2 i j = -(raw17688step1 i j); unfold raw17688step2 raw17688step1; decide +kernel
      have hl : raw17688step2Labels = raw17688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw17689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17689 raw17689Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw17689 raw17689Labels = mixedMoment B raw17689step0 raw17689step0Labels := by
      have ha : raw17689step0 = (fun i j => raw17689 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17689step0 raw17689; decide +kernel
      have hl : raw17689step0Labels = raw17689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17689 raw17689Labels permutation646 permutation2
    mixedMoment B raw17689step0 raw17689step0Labels = mixedMoment B raw17689step1 raw17689step1Labels := by
      have ha : raw17689step1 = -raw17689step0 := by apply Matrix.ext; change ∀ i j, raw17689step1 i j = -(raw17689step0 i j); unfold raw17689step1 raw17689step0; decide +kernel
      have hl : raw17689step1Labels = raw17689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw17690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17690 raw17690Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17690 raw17690Labels = mixedMoment B raw17690step0 raw17690step0Labels := by
      have hz : ∀ j, raw17690 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17690step0 = (fun i j => raw17690 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17690step0 raw17690; decide +kernel
      have hl : raw17690step0Labels = raw17690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17690 raw17690Labels permutation520 hz
    mixedMoment B raw17690step0 raw17690step0Labels = mixedMoment B raw17690step1 raw17690step1Labels := by
      have hz : ∀ j, raw17690step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17690step1 = (fun i j => raw17690step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17690step1 raw17690step0; decide +kernel
      have hl : raw17690step1Labels = raw17690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17690step0 raw17690step0Labels permutation104 hz
    mixedMoment B raw17690step1 raw17690step1Labels = mixedMoment B raw17690step2 raw17690step2Labels := by
      have ha : raw17690step2 = (fun i j => raw17690step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17690step2 raw17690step1; decide +kernel
      have hl : raw17690step2Labels = raw17690step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17690step1 raw17690step1Labels permutation31 permutation2
    mixedMoment B raw17690step2 raw17690step2Labels = mixedMoment B raw17690step3 raw17690step3Labels := by
      have ha : raw17690step3 = -raw17690step2 := by apply Matrix.ext; change ∀ i j, raw17690step3 i j = -(raw17690step2 i j); unfold raw17690step3 raw17690step2; decide +kernel
      have hl : raw17690step3Labels = raw17690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17691 raw17691Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw17691 raw17691Labels = mixedMoment B raw17691step0 raw17691step0Labels := by
      have hz : ∀ j, raw17691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17691step0 = (fun i j => raw17691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17691step0 raw17691; decide +kernel
      have hl : raw17691step0Labels = raw17691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17691 raw17691Labels permutation346 hz
    mixedMoment B raw17691step0 raw17691step0Labels = mixedMoment B raw17691step1 raw17691step1Labels := by
      have ha : raw17691step1 = (fun i j => raw17691step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17691step1 raw17691step0; decide +kernel
      have hl : raw17691step1Labels = raw17691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17691step0 raw17691step0Labels permutation144 permutation2
    mixedMoment B raw17691step1 raw17691step1Labels = mixedMoment B raw17691step2 raw17691step2Labels := by
      have ha : raw17691step2 = -raw17691step1 := by apply Matrix.ext; change ∀ i j, raw17691step2 i j = -(raw17691step1 i j); unfold raw17691step2 raw17691step1; decide +kernel
      have hl : raw17691step2Labels = raw17691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw17692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17692 raw17692Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw17692 raw17692Labels = mixedMoment B raw17692step0 raw17692step0Labels := by
      have ha : raw17692step0 = (fun i j => raw17692 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17692step0 raw17692; decide +kernel
      have hl : raw17692step0Labels = raw17692Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17692 raw17692Labels permutation664 permutation2
    mixedMoment B raw17692step0 raw17692step0Labels = mixedMoment B raw17692step1 raw17692step1Labels := by
      have ha : raw17692step1 = -raw17692step0 := by apply Matrix.ext; change ∀ i j, raw17692step1 i j = -(raw17692step0 i j); unfold raw17692step1 raw17692step0; decide +kernel
      have hl : raw17692step1Labels = raw17692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw17693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17693 raw17693Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17693 raw17693Labels = mixedMoment B raw17693step0 raw17693step0Labels := by
      have hz : ∀ j, raw17693 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17693step0 = (fun i j => raw17693 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17693step0 raw17693; decide +kernel
      have hl : raw17693step0Labels = raw17693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17693 raw17693Labels permutation520 hz
    mixedMoment B raw17693step0 raw17693step0Labels = mixedMoment B raw17693step1 raw17693step1Labels := by
      have hz : ∀ j, raw17693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17693step1 = (fun i j => raw17693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17693step1 raw17693step0; decide +kernel
      have hl : raw17693step1Labels = raw17693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17693step0 raw17693step0Labels permutation80 hz
    mixedMoment B raw17693step1 raw17693step1Labels = mixedMoment B raw17693step2 raw17693step2Labels := by
      have ha : raw17693step2 = (fun i j => raw17693step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17693step2 raw17693step1; decide +kernel
      have hl : raw17693step2Labels = raw17693step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17693step1 raw17693step1Labels permutation31 permutation2
    mixedMoment B raw17693step2 raw17693step2Labels = mixedMoment B raw17693step3 raw17693step3Labels := by
      have ha : raw17693step3 = -raw17693step2 := by apply Matrix.ext; change ∀ i j, raw17693step3 i j = -(raw17693step2 i j); unfold raw17693step3 raw17693step2; decide +kernel
      have hl : raw17693step3Labels = raw17693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17694 raw17694Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw17694 raw17694Labels = mixedMoment B raw17694step0 raw17694step0Labels := by
      have hz : ∀ j, raw17694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17694step0 = (fun i j => raw17694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17694step0 raw17694; decide +kernel
      have hl : raw17694step0Labels = raw17694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694 raw17694Labels permutation434 hz
    mixedMoment B raw17694step0 raw17694step0Labels = mixedMoment B raw17694step1 raw17694step1Labels := by
      have hz : ∀ j, raw17694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17694step1 = (fun i j => raw17694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17694step1 raw17694step0; decide +kernel
      have hl : raw17694step1Labels = raw17694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17694step0 raw17694step0Labels permutation80 hz
    mixedMoment B raw17694step1 raw17694step1Labels = mixedMoment B raw17694step2 raw17694step2Labels := by
      have ha : raw17694step2 = (fun i j => raw17694step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17694step2 raw17694step1; decide +kernel
      have hl : raw17694step2Labels = raw17694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17694step1 raw17694step1Labels permutation9 permutation3
    mixedMoment B raw17694step2 raw17694step2Labels = mixedMoment B raw17694step3 raw17694step3Labels := by
      have ha : raw17694step3 = raw17694step2 := by apply Matrix.ext; unfold raw17694step3 raw17694step2; decide +kernel
      have hl : raw17694step2Labels = labelEmbedding6 ∘ raw17694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17694step2 raw17694step2Labels raw17694step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw17695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17695 raw17695Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw17695 raw17695Labels = mixedMoment B raw17695step0 raw17695step0Labels := by
      have hz : ∀ j, raw17695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17695step0 = (fun i j => raw17695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17695step0 raw17695; decide +kernel
      have hl : raw17695step0Labels = raw17695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17695 raw17695Labels permutation434 hz
    mixedMoment B raw17695step0 raw17695step0Labels = mixedMoment B raw17695step1 raw17695step1Labels := by
      have hz : ∀ j, raw17695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17695step1 = (fun i j => raw17695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17695step1 raw17695step0; decide +kernel
      have hl : raw17695step1Labels = raw17695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17695step0 raw17695step0Labels permutation80 hz
    mixedMoment B raw17695step1 raw17695step1Labels = mixedMoment B raw17695step2 raw17695step2Labels := by
      have ha : raw17695step2 = (fun i j => raw17695step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17695step2 raw17695step1; decide +kernel
      have hl : raw17695step2Labels = raw17695step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17695step1 raw17695step1Labels permutation30 permutation2
    mixedMoment B raw17695step2 raw17695step2Labels = mixedMoment B raw17695step3 raw17695step3Labels := by
      have ha : raw17695step3 = -raw17695step2 := by apply Matrix.ext; change ∀ i j, raw17695step3 i j = -(raw17695step2 i j); unfold raw17695step3 raw17695step2; decide +kernel
      have hl : raw17695step3Labels = raw17695step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw17696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17696 raw17696Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw17696 raw17696Labels = mixedMoment B raw17696step0 raw17696step0Labels := by
      have hz : ∀ j, raw17696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17696step0 = (fun i j => raw17696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17696step0 raw17696; decide +kernel
      have hl : raw17696step0Labels = raw17696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17696 raw17696Labels permutation434 hz
    mixedMoment B raw17696step0 raw17696step0Labels = mixedMoment B raw17696step1 raw17696step1Labels := by
      have ha : raw17696step1 = (fun i j => raw17696step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17696step1 raw17696step0; decide +kernel
      have hl : raw17696step1Labels = raw17696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17696step0 raw17696step0Labels permutation151 permutation2
    mixedMoment B raw17696step1 raw17696step1Labels = mixedMoment B raw17696step2 raw17696step2Labels := by
      have ha : raw17696step2 = -raw17696step1 := by apply Matrix.ext; change ∀ i j, raw17696step2 i j = -(raw17696step1 i j); unfold raw17696step2 raw17696step1; decide +kernel
      have hl : raw17696step2Labels = raw17696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw17697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17697 raw17697Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw17697 raw17697Labels = mixedMoment B raw17697step0 raw17697step0Labels := by
      have hz : ∀ j, raw17697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17697step0 = (fun i j => raw17697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17697step0 raw17697; decide +kernel
      have hl : raw17697step0Labels = raw17697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17697 raw17697Labels permutation346 hz
    mixedMoment B raw17697step0 raw17697step0Labels = mixedMoment B raw17697step1 raw17697step1Labels := by
      have ha : raw17697step1 = (fun i j => raw17697step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17697step1 raw17697step0; decide +kernel
      have hl : raw17697step1Labels = raw17697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17697step0 raw17697step0Labels permutation151 permutation2
    mixedMoment B raw17697step1 raw17697step1Labels = mixedMoment B raw17697step2 raw17697step2Labels := by
      have ha : raw17697step2 = -raw17697step1 := by apply Matrix.ext; change ∀ i j, raw17697step2 i j = -(raw17697step1 i j); unfold raw17697step2 raw17697step1; decide +kernel
      have hl : raw17697step2Labels = raw17697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw17698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw17698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw17698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17698 raw17698Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw17698 raw17698Labels = mixedMoment B raw17698step0 raw17698step0Labels := by
      have hz : ∀ j, raw17698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17698step0 = (fun i j => raw17698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17698step0 raw17698; decide +kernel
      have hl : raw17698step0Labels = raw17698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17698 raw17698Labels permutation434 hz
    mixedMoment B raw17698step0 raw17698step0Labels = mixedMoment B raw17698step1 raw17698step1Labels := by
      have hz : ∀ j, raw17698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17698step1 = (fun i j => raw17698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17698step1 raw17698step0; decide +kernel
      have hl : raw17698step1Labels = raw17698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17698step0 raw17698step0Labels permutation80 hz
    mixedMoment B raw17698step1 raw17698step1Labels = mixedMoment B raw17698step2 raw17698step2Labels := by
      have ha : raw17698step2 = (fun i j => raw17698step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17698step2 raw17698step1; decide +kernel
      have hl : raw17698step2Labels = raw17698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17698step1 raw17698step1Labels permutation31 permutation2
    mixedMoment B raw17698step2 raw17698step2Labels = mixedMoment B raw17698step3 raw17698step3Labels := by
      have ha : raw17698step3 = -raw17698step2 := by apply Matrix.ext; change ∀ i j, raw17698step3 i j = -(raw17698step2 i j); unfold raw17698step3 raw17698step2; decide +kernel
      have hl : raw17698step3Labels = raw17698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw17699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw17699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw17699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17699 raw17699Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw17699 raw17699Labels = mixedMoment B raw17699step0 raw17699step0Labels := by
      have hz : ∀ j, raw17699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17699step0 = (fun i j => raw17699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17699step0 raw17699; decide +kernel
      have hl : raw17699step0Labels = raw17699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17699 raw17699Labels permutation434 hz
    mixedMoment B raw17699step0 raw17699step0Labels = mixedMoment B raw17699step1 raw17699step1Labels := by
      have hz : ∀ j, raw17699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17699step1 = (fun i j => raw17699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17699step1 raw17699step0; decide +kernel
      have hl : raw17699step1Labels = raw17699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17699step0 raw17699step0Labels permutation80 hz
    mixedMoment B raw17699step1 raw17699step1Labels = mixedMoment B raw17699step2 raw17699step2Labels := by
      have ha : raw17699step2 = (fun i j => raw17699step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17699step2 raw17699step1; decide +kernel
      have hl : raw17699step2Labels = raw17699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17699step1 raw17699step1Labels permutation30 permutation2
    mixedMoment B raw17699step2 raw17699step2Labels = mixedMoment B raw17699step3 raw17699step3Labels := by
      have ha : raw17699step3 = -raw17699step2 := by apply Matrix.ext; change ∀ i j, raw17699step3 i j = -(raw17699step2 i j); unfold raw17699step3 raw17699step2; decide +kernel
      have hl : raw17699step3Labels = raw17699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw17700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17700 raw17700Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17700 raw17700Labels = mixedMoment B raw17700step0 raw17700step0Labels := by
      have hz : ∀ j, raw17700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17700step0 = (fun i j => raw17700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17700step0 raw17700; decide +kernel
      have hl : raw17700step0Labels = raw17700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17700 raw17700Labels permutation434 hz
    mixedMoment B raw17700step0 raw17700step0Labels = mixedMoment B raw17700step1 raw17700step1Labels := by
      have ha : raw17700step1 = (fun i j => raw17700step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17700step1 raw17700step0; decide +kernel
      have hl : raw17700step1Labels = raw17700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17700step0 raw17700step0Labels permutation151 permutation2
    mixedMoment B raw17700step1 raw17700step1Labels = mixedMoment B raw17700step2 raw17700step2Labels := by
      have ha : raw17700step2 = -raw17700step1 := by apply Matrix.ext; change ∀ i j, raw17700step2 i j = -(raw17700step1 i j); unfold raw17700step2 raw17700step1; decide +kernel
      have hl : raw17700step2Labels = raw17700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17701 raw17701Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw17701 raw17701Labels = mixedMoment B raw17701step0 raw17701step0Labels := by
      have hz : ∀ j, raw17701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17701step0 = (fun i j => raw17701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17701step0 raw17701; decide +kernel
      have hl : raw17701step0Labels = raw17701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17701 raw17701Labels permutation346 hz
    mixedMoment B raw17701step0 raw17701step0Labels = mixedMoment B raw17701step1 raw17701step1Labels := by
      have ha : raw17701step1 = (fun i j => raw17701step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17701step1 raw17701step0; decide +kernel
      have hl : raw17701step1Labels = raw17701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17701step0 raw17701step0Labels permutation151 permutation2
    mixedMoment B raw17701step1 raw17701step1Labels = mixedMoment B raw17701step2 raw17701step2Labels := by
      have ha : raw17701step2 = -raw17701step1 := by apply Matrix.ext; change ∀ i j, raw17701step2 i j = -(raw17701step1 i j); unfold raw17701step2 raw17701step1; decide +kernel
      have hl : raw17701step2Labels = raw17701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw17702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw17702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17702step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17702step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw17702step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17702 raw17702Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw17702 raw17702Labels = mixedMoment B raw17702step0 raw17702step0Labels := by
      have hz : ∀ j, raw17702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17702step0 = (fun i j => raw17702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17702step0 raw17702; decide +kernel
      have hl : raw17702step0Labels = raw17702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17702 raw17702Labels permutation520 hz
    mixedMoment B raw17702step0 raw17702step0Labels = mixedMoment B raw17702step1 raw17702step1Labels := by
      have hz : ∀ j, raw17702step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17702step1 = (fun i j => raw17702step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17702step1 raw17702step0; decide +kernel
      have hl : raw17702step1Labels = raw17702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17702step0 raw17702step0Labels permutation104 hz
    mixedMoment B raw17702step1 raw17702step1Labels = mixedMoment B raw17702step2 raw17702step2Labels := by
      have hz : ∀ j, raw17702step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw17702step2 = (fun i j => raw17702step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw17702step2 raw17702step1; decide +kernel
      have hl : raw17702step2Labels = raw17702step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17702step1 raw17702step1Labels permutation20 hz
    mixedMoment B raw17702step2 raw17702step2Labels = mixedMoment B raw17702step3 raw17702step3Labels := by
      have ha : raw17702step3 = (fun i j => raw17702step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17702step3 raw17702step2; decide +kernel
      have hl : raw17702step3Labels = raw17702step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17702step2 raw17702step2Labels permutation7 permutation2
    mixedMoment B raw17702step3 raw17702step3Labels = mixedMoment B raw17702step4 raw17702step4Labels := by
      have ha : raw17702step4 = -raw17702step3 := by apply Matrix.ext; change ∀ i j, raw17702step4 i j = -(raw17702step3 i j); unfold raw17702step4 raw17702step3; decide +kernel
      have hl : raw17702step4Labels = raw17702step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw17703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17703 raw17703Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17703 raw17703Labels = mixedMoment B raw17703step0 raw17703step0Labels := by
      have hz : ∀ j, raw17703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17703step0 = (fun i j => raw17703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17703step0 raw17703; decide +kernel
      have hl : raw17703step0Labels = raw17703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17703 raw17703Labels permutation346 hz
    mixedMoment B raw17703step0 raw17703step0Labels = mixedMoment B raw17703step1 raw17703step1Labels := by
      have ha : raw17703step1 = (fun i j => raw17703step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17703step1 raw17703step0; decide +kernel
      have hl : raw17703step1Labels = raw17703step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17703step0 raw17703step0Labels permutation150 permutation2
    mixedMoment B raw17703step1 raw17703step1Labels = mixedMoment B raw17703step2 raw17703step2Labels := by
      have ha : raw17703step2 = -raw17703step1 := by apply Matrix.ext; change ∀ i j, raw17703step2 i j = -(raw17703step1 i j); unfold raw17703step2 raw17703step1; decide +kernel
      have hl : raw17703step2Labels = raw17703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17704 raw17704Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw17704 raw17704Labels = mixedMoment B raw17704step0 raw17704step0Labels := by
      have ha : raw17704step0 = (fun i j => raw17704 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17704step0 raw17704; decide +kernel
      have hl : raw17704step0Labels = raw17704Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17704 raw17704Labels permutation687 permutation2
    mixedMoment B raw17704step0 raw17704step0Labels = mixedMoment B raw17704step1 raw17704step1Labels := by
      have ha : raw17704step1 = -raw17704step0 := by apply Matrix.ext; change ∀ i j, raw17704step1 i j = -(raw17704step0 i j); unfold raw17704step1 raw17704step0; decide +kernel
      have hl : raw17704step1Labels = raw17704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw17705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17705 raw17705Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw17705 raw17705Labels = mixedMoment B raw17705step0 raw17705step0Labels := by
      have hz : ∀ j, raw17705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17705step0 = (fun i j => raw17705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17705step0 raw17705; decide +kernel
      have hl : raw17705step0Labels = raw17705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17705 raw17705Labels permutation346 hz
    mixedMoment B raw17705step0 raw17705step0Labels = mixedMoment B raw17705step1 raw17705step1Labels := by
      have ha : raw17705step1 = (fun i j => raw17705step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17705step1 raw17705step0; decide +kernel
      have hl : raw17705step1Labels = raw17705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17705step0 raw17705step0Labels permutation146 permutation2
    mixedMoment B raw17705step1 raw17705step1Labels = mixedMoment B raw17705step2 raw17705step2Labels := by
      have ha : raw17705step2 = -raw17705step1 := by apply Matrix.ext; change ∀ i j, raw17705step2 i j = -(raw17705step1 i j); unfold raw17705step2 raw17705step1; decide +kernel
      have hl : raw17705step2Labels = raw17705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw17706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17706 raw17706Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw17706 raw17706Labels = mixedMoment B raw17706step0 raw17706step0Labels := by
      have hz : ∀ j, raw17706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17706step0 = (fun i j => raw17706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17706step0 raw17706; decide +kernel
      have hl : raw17706step0Labels = raw17706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17706 raw17706Labels permutation346 hz
    mixedMoment B raw17706step0 raw17706step0Labels = mixedMoment B raw17706step1 raw17706step1Labels := by
      have ha : raw17706step1 = (fun i j => raw17706step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17706step1 raw17706step0; decide +kernel
      have hl : raw17706step1Labels = raw17706step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17706step0 raw17706step0Labels permutation122 permutation6
    mixedMoment B raw17706step1 raw17706step1Labels = mixedMoment B raw17706step2 raw17706step2Labels := by
      have ha : raw17706step2 = raw17706step1 := by apply Matrix.ext; unfold raw17706step2 raw17706step1; decide +kernel
      have hl : raw17706step1Labels = labelEmbedding9 ∘ raw17706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17706step1 raw17706step1Labels raw17706step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw17707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17707 raw17707Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17707 raw17707Labels = mixedMoment B raw17707step0 raw17707step0Labels := by
      have hz : ∀ j, raw17707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17707step0 = (fun i j => raw17707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17707step0 raw17707; decide +kernel
      have hl : raw17707step0Labels = raw17707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17707 raw17707Labels permutation346 hz
    mixedMoment B raw17707step0 raw17707step0Labels = mixedMoment B raw17707step1 raw17707step1Labels := by
      have ha : raw17707step1 = (fun i j => raw17707step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17707step1 raw17707step0; decide +kernel
      have hl : raw17707step1Labels = raw17707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17707step0 raw17707step0Labels permutation126 permutation7
    mixedMoment B raw17707step1 raw17707step1Labels = mixedMoment B raw17707step2 raw17707step2Labels := by
      have ha : raw17707step2 = raw17707step1 := by apply Matrix.ext; unfold raw17707step2 raw17707step1; decide +kernel
      have hl : raw17707step1Labels = labelEmbedding10 ∘ raw17707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17707step1 raw17707step1Labels raw17707step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17708 raw17708Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw17708 raw17708Labels = mixedMoment B raw17708step0 raw17708step0Labels := by
      have hz : ∀ j, raw17708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17708step0 = (fun i j => raw17708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17708step0 raw17708; decide +kernel
      have hl : raw17708step0Labels = raw17708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17708 raw17708Labels permutation346 hz
    mixedMoment B raw17708step0 raw17708step0Labels = mixedMoment B raw17708step1 raw17708step1Labels := by
      have ha : raw17708step1 = (fun i j => raw17708step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17708step1 raw17708step0; decide +kernel
      have hl : raw17708step1Labels = raw17708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17708step0 raw17708step0Labels permutation32 permutation3
    mixedMoment B raw17708step1 raw17708step1Labels = mixedMoment B raw17708step2 raw17708step2Labels := by
      have ha : raw17708step2 = raw17708step1 := by apply Matrix.ext; unfold raw17708step2 raw17708step1; decide +kernel
      have hl : raw17708step1Labels = labelEmbedding6 ∘ raw17708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17708step1 raw17708step1Labels raw17708step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw17709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17709 raw17709Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17709 raw17709Labels = mixedMoment B raw17709step0 raw17709step0Labels := by
      have ha : raw17709step0 = (fun i j => raw17709 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17709step0 raw17709; decide +kernel
      have hl : raw17709step0Labels = raw17709Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17709 raw17709Labels permutation676 permutation2
    mixedMoment B raw17709step0 raw17709step0Labels = mixedMoment B raw17709step1 raw17709step1Labels := by
      have ha : raw17709step1 = -raw17709step0 := by apply Matrix.ext; change ∀ i j, raw17709step1 i j = -(raw17709step0 i j); unfold raw17709step1 raw17709step0; decide +kernel
      have hl : raw17709step1Labels = raw17709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw17710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17710 raw17710Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17710 raw17710Labels = mixedMoment B raw17710step0 raw17710step0Labels := by
      have hz : ∀ j, raw17710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17710step0 = (fun i j => raw17710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17710step0 raw17710; decide +kernel
      have hl : raw17710step0Labels = raw17710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17710 raw17710Labels permutation346 hz
    mixedMoment B raw17710step0 raw17710step0Labels = mixedMoment B raw17710step1 raw17710step1Labels := by
      have ha : raw17710step1 = (fun i j => raw17710step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17710step1 raw17710step0; decide +kernel
      have hl : raw17710step1Labels = raw17710step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17710step0 raw17710step0Labels permutation149 permutation2
    mixedMoment B raw17710step1 raw17710step1Labels = mixedMoment B raw17710step2 raw17710step2Labels := by
      have ha : raw17710step2 = -raw17710step1 := by apply Matrix.ext; change ∀ i j, raw17710step2 i j = -(raw17710step1 i j); unfold raw17710step2 raw17710step1; decide +kernel
      have hl : raw17710step2Labels = raw17710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17711step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17711 raw17711Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw17711 raw17711Labels = mixedMoment B raw17711step0 raw17711step0Labels := by
      have hz : ∀ j, raw17711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17711step0 = (fun i j => raw17711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17711step0 raw17711; decide +kernel
      have hl : raw17711step0Labels = raw17711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17711 raw17711Labels permutation346 hz
    mixedMoment B raw17711step0 raw17711step0Labels = mixedMoment B raw17711step1 raw17711step1Labels := by
      have ha : raw17711step1 = (fun i j => raw17711step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17711step1 raw17711step0; decide +kernel
      have hl : raw17711step1Labels = raw17711step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17711step0 raw17711step0Labels permutation108 permutation4
    mixedMoment B raw17711step1 raw17711step1Labels = mixedMoment B raw17711step2 raw17711step2Labels := by
      have ha : raw17711step2 = -raw17711step1 := by apply Matrix.ext; change ∀ i j, raw17711step2 i j = -(raw17711step1 i j); unfold raw17711step2 raw17711step1; decide +kernel
      have hl : raw17711step2Labels = raw17711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17711step2 raw17711step2Labels = mixedMoment B raw17711step3 raw17711step3Labels := by
      have ha : raw17711step3 = raw17711step2 := by apply Matrix.ext; unfold raw17711step3 raw17711step2; decide +kernel
      have hl : raw17711step2Labels = labelEmbedding7 ∘ raw17711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17711step2 raw17711step2Labels raw17711step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw17712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17712 raw17712Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17712 raw17712Labels = mixedMoment B raw17712step0 raw17712step0Labels := by
      have hz : ∀ j, raw17712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17712step0 = (fun i j => raw17712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17712step0 raw17712; decide +kernel
      have hl : raw17712step0Labels = raw17712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17712 raw17712Labels permutation346 hz
    mixedMoment B raw17712step0 raw17712step0Labels = mixedMoment B raw17712step1 raw17712step1Labels := by
      have ha : raw17712step1 = (fun i j => raw17712step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17712step1 raw17712step0; decide +kernel
      have hl : raw17712step1Labels = raw17712step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17712step0 raw17712step0Labels permutation125 permutation7
    mixedMoment B raw17712step1 raw17712step1Labels = mixedMoment B raw17712step2 raw17712step2Labels := by
      have ha : raw17712step2 = raw17712step1 := by apply Matrix.ext; unfold raw17712step2 raw17712step1; decide +kernel
      have hl : raw17712step1Labels = labelEmbedding10 ∘ raw17712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17712step1 raw17712step1Labels raw17712step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw17713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17713 raw17713Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw17713 raw17713Labels = mixedMoment B raw17713step0 raw17713step0Labels := by
      have ha : raw17713step0 = (fun i j => raw17713 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17713step0 raw17713; decide +kernel
      have hl : raw17713step0Labels = raw17713Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17713 raw17713Labels permutation160 permutation3
    mixedMoment B raw17713step0 raw17713step0Labels = mixedMoment B raw17713step1 raw17713step1Labels := by
      have ha : raw17713step1 = raw17713step0 := by apply Matrix.ext; unfold raw17713step1 raw17713step0; decide +kernel
      have hl : raw17713step0Labels = labelEmbedding6 ∘ raw17713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17713step0 raw17713step0Labels raw17713step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw17714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17714 raw17714Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw17714 raw17714Labels = mixedMoment B raw17714step0 raw17714step0Labels := by
      have ha : raw17714step0 = (fun i j => raw17714 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17714step0 raw17714; decide +kernel
      have hl : raw17714step0Labels = raw17714Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17714 raw17714Labels permutation158 permutation2
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw17715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17715 raw17715Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw17715 raw17715Labels = mixedMoment B raw17715step0 raw17715step0Labels := by
      have ha : raw17715step0 = (fun i j => raw17715 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17715step0 raw17715; decide +kernel
      have hl : raw17715step0Labels = raw17715Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17715 raw17715Labels permutation680 permutation2
    mixedMoment B raw17715step0 raw17715step0Labels = mixedMoment B raw17715step1 raw17715step1Labels := by
      have ha : raw17715step1 = -raw17715step0 := by apply Matrix.ext; change ∀ i j, raw17715step1 i j = -(raw17715step0 i j); unfold raw17715step1 raw17715step0; decide +kernel
      have hl : raw17715step1Labels = raw17715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw17716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17716 raw17716Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17716 raw17716Labels = mixedMoment B raw17716step0 raw17716step0Labels := by
      have ha : raw17716step0 = (fun i j => raw17716 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17716step0 raw17716; decide +kernel
      have hl : raw17716step0Labels = raw17716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17716 raw17716Labels permutation524 permutation4
    mixedMoment B raw17716step0 raw17716step0Labels = mixedMoment B raw17716step1 raw17716step1Labels := by
      have ha : raw17716step1 = -raw17716step0 := by apply Matrix.ext; change ∀ i j, raw17716step1 i j = -(raw17716step0 i j); unfold raw17716step1 raw17716step0; decide +kernel
      have hl : raw17716step1Labels = raw17716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17716step1 raw17716step1Labels = mixedMoment B raw17716step2 raw17716step2Labels := by
      have ha : raw17716step2 = raw17716step1 := by apply Matrix.ext; unfold raw17716step2 raw17716step1; decide +kernel
      have hl : raw17716step1Labels = labelEmbedding7 ∘ raw17716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17716step1 raw17716step1Labels raw17716step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw17717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17717 raw17717Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17717 raw17717Labels = mixedMoment B raw17717step0 raw17717step0Labels := by
      have ha : raw17717step0 = (fun i j => raw17717 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17717step0 raw17717; decide +kernel
      have hl : raw17717step0Labels = raw17717Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17717 raw17717Labels permutation159 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw17718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17718step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17718 raw17718Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw17718 raw17718Labels = mixedMoment B raw17718step0 raw17718step0Labels := by
      have hz : ∀ j, raw17718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17718step0 = (fun i j => raw17718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17718step0 raw17718; decide +kernel
      have hl : raw17718step0Labels = raw17718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17718 raw17718Labels permutation346 hz
    mixedMoment B raw17718step0 raw17718step0Labels = mixedMoment B raw17718step1 raw17718step1Labels := by
      have ha : raw17718step1 = (fun i j => raw17718step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17718step1 raw17718step0; decide +kernel
      have hl : raw17718step1Labels = raw17718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17718step0 raw17718step0Labels permutation34 permutation3
    mixedMoment B raw17718step1 raw17718step1Labels = mixedMoment B raw17718step2 raw17718step2Labels := by
      have ha : raw17718step2 = raw17718step1 := by apply Matrix.ext; unfold raw17718step2 raw17718step1; decide +kernel
      have hl : raw17718step1Labels = labelEmbedding6 ∘ raw17718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17718step1 raw17718step1Labels raw17718step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw17719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17719 raw17719Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw17719 raw17719Labels = mixedMoment B raw17719step0 raw17719step0Labels := by
      have hz : ∀ j, raw17719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17719step0 = (fun i j => raw17719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17719step0 raw17719; decide +kernel
      have hl : raw17719step0Labels = raw17719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17719 raw17719Labels permutation346 hz
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw17720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17720 raw17720Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw17720 raw17720Labels = mixedMoment B raw17720step0 raw17720step0Labels := by
      have ha : raw17720step0 = (fun i j => raw17720 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17720step0 raw17720; decide +kernel
      have hl : raw17720step0Labels = raw17720Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17720 raw17720Labels permutation688 permutation2
    mixedMoment B raw17720step0 raw17720step0Labels = mixedMoment B raw17720step1 raw17720step1Labels := by
      have ha : raw17720step1 = -raw17720step0 := by apply Matrix.ext; change ∀ i j, raw17720step1 i j = -(raw17720step0 i j); unfold raw17720step1 raw17720step0; decide +kernel
      have hl : raw17720step1Labels = raw17720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw17721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17721step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17721 raw17721Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17721 raw17721Labels = mixedMoment B raw17721step0 raw17721step0Labels := by
      have hz : ∀ j, raw17721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17721step0 = (fun i j => raw17721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17721step0 raw17721; decide +kernel
      have hl : raw17721step0Labels = raw17721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17721 raw17721Labels permutation346 hz
    mixedMoment B raw17721step0 raw17721step0Labels = mixedMoment B raw17721step1 raw17721step1Labels := by
      have ha : raw17721step1 = (fun i j => raw17721step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17721step1 raw17721step0; decide +kernel
      have hl : raw17721step1Labels = raw17721step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17721step0 raw17721step0Labels permutation105 permutation4
    mixedMoment B raw17721step1 raw17721step1Labels = mixedMoment B raw17721step2 raw17721step2Labels := by
      have ha : raw17721step2 = -raw17721step1 := by apply Matrix.ext; change ∀ i j, raw17721step2 i j = -(raw17721step1 i j); unfold raw17721step2 raw17721step1; decide +kernel
      have hl : raw17721step2Labels = raw17721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17721step2 raw17721step2Labels = mixedMoment B raw17721step3 raw17721step3Labels := by
      have ha : raw17721step3 = raw17721step2 := by apply Matrix.ext; unfold raw17721step3 raw17721step2; decide +kernel
      have hl : raw17721step2Labels = labelEmbedding7 ∘ raw17721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17721step2 raw17721step2Labels raw17721step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17722 raw17722Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw17722 raw17722Labels = mixedMoment B raw17722step0 raw17722step0Labels := by
      have hz : ∀ j, raw17722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17722step0 = (fun i j => raw17722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17722step0 raw17722; decide +kernel
      have hl : raw17722step0Labels = raw17722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17722 raw17722Labels permutation346 hz
    mixedMoment B raw17722step0 raw17722step0Labels = mixedMoment B raw17722step1 raw17722step1Labels := by
      have ha : raw17722step1 = (fun i j => raw17722step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17722step1 raw17722step0; decide +kernel
      have hl : raw17722step1Labels = raw17722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17722step0 raw17722step0Labels permutation33 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw17723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17723 raw17723Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw17723 raw17723Labels = mixedMoment B raw17723step0 raw17723step0Labels := by
      have hz : ∀ j, raw17723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17723step0 = (fun i j => raw17723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17723step0 raw17723; decide +kernel
      have hl : raw17723step0Labels = raw17723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17723 raw17723Labels permutation346 hz
    mixedMoment B raw17723step0 raw17723step0Labels = mixedMoment B raw17723step1 raw17723step1Labels := by
      have ha : raw17723step1 = (fun i j => raw17723step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17723step1 raw17723step0; decide +kernel
      have hl : raw17723step1Labels = raw17723step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17723step0 raw17723step0Labels permutation32 permutation3
    mixedMoment B raw17723step1 raw17723step1Labels = mixedMoment B raw17723step2 raw17723step2Labels := by
      have ha : raw17723step2 = raw17723step1 := by apply Matrix.ext; unfold raw17723step2 raw17723step1; decide +kernel
      have hl : raw17723step1Labels = labelEmbedding6 ∘ raw17723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17723step1 raw17723step1Labels raw17723step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw17724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17724 raw17724Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw17724 raw17724Labels = mixedMoment B raw17724step0 raw17724step0Labels := by
      have hz : ∀ j, raw17724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17724step0 = (fun i j => raw17724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17724step0 raw17724; decide +kernel
      have hl : raw17724step0Labels = raw17724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17724 raw17724Labels permutation346 hz
    mixedMoment B raw17724step0 raw17724step0Labels = mixedMoment B raw17724step1 raw17724step1Labels := by
      have ha : raw17724step1 = (fun i j => raw17724step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17724step1 raw17724step0; decide +kernel
      have hl : raw17724step1Labels = raw17724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17724step0 raw17724step0Labels permutation126 permutation2
    mixedMoment B raw17724step1 raw17724step1Labels = mixedMoment B raw17724step2 raw17724step2Labels := by
      have ha : raw17724step2 = -raw17724step1 := by apply Matrix.ext; change ∀ i j, raw17724step2 i j = -(raw17724step1 i j); unfold raw17724step2 raw17724step1; decide +kernel
      have hl : raw17724step2Labels = raw17724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw17725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17725 raw17725Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17725 raw17725Labels = mixedMoment B raw17725step0 raw17725step0Labels := by
      have ha : raw17725step0 = (fun i j => raw17725 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17725step0 raw17725; decide +kernel
      have hl : raw17725step0Labels = raw17725Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17725 raw17725Labels permutation589 permutation2
    mixedMoment B raw17725step0 raw17725step0Labels = mixedMoment B raw17725step1 raw17725step1Labels := by
      have ha : raw17725step1 = -raw17725step0 := by apply Matrix.ext; change ∀ i j, raw17725step1 i j = -(raw17725step0 i j); unfold raw17725step1 raw17725step0; decide +kernel
      have hl : raw17725step1Labels = raw17725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17726 raw17726Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw17726 raw17726Labels = mixedMoment B raw17726step0 raw17726step0Labels := by
      have hz : ∀ j, raw17726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17726step0 = (fun i j => raw17726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17726step0 raw17726; decide +kernel
      have hl : raw17726step0Labels = raw17726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17726 raw17726Labels permutation346 hz
    mixedMoment B raw17726step0 raw17726step0Labels = mixedMoment B raw17726step1 raw17726step1Labels := by
      have ha : raw17726step1 = (fun i j => raw17726step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17726step1 raw17726step0; decide +kernel
      have hl : raw17726step1Labels = raw17726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17726step0 raw17726step0Labels permutation125 permutation2
    mixedMoment B raw17726step1 raw17726step1Labels = mixedMoment B raw17726step2 raw17726step2Labels := by
      have ha : raw17726step2 = -raw17726step1 := by apply Matrix.ext; change ∀ i j, raw17726step2 i j = -(raw17726step1 i j); unfold raw17726step2 raw17726step1; decide +kernel
      have hl : raw17726step2Labels = raw17726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw17727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17727 raw17727Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17727 raw17727Labels = mixedMoment B raw17727step0 raw17727step0Labels := by
      have hz : ∀ j, raw17727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17727step0 = (fun i j => raw17727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17727step0 raw17727; decide +kernel
      have hl : raw17727step0Labels = raw17727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17727 raw17727Labels permutation346 hz
    mixedMoment B raw17727step0 raw17727step0Labels = mixedMoment B raw17727step1 raw17727step1Labels := by
      have ha : raw17727step1 = (fun i j => raw17727step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17727step1 raw17727step0; decide +kernel
      have hl : raw17727step1Labels = raw17727step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17727step0 raw17727step0Labels permutation127 permutation2
    mixedMoment B raw17727step1 raw17727step1Labels = mixedMoment B raw17727step2 raw17727step2Labels := by
      have ha : raw17727step2 = -raw17727step1 := by apply Matrix.ext; change ∀ i j, raw17727step2 i j = -(raw17727step1 i j); unfold raw17727step2 raw17727step1; decide +kernel
      have hl : raw17727step2Labels = raw17727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17728step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17728 raw17728Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw17728 raw17728Labels = mixedMoment B raw17728step0 raw17728step0Labels := by
      have hz : ∀ j, raw17728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17728step0 = (fun i j => raw17728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17728step0 raw17728; decide +kernel
      have hl : raw17728step0Labels = raw17728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17728 raw17728Labels permutation346 hz
    mixedMoment B raw17728step0 raw17728step0Labels = mixedMoment B raw17728step1 raw17728step1Labels := by
      have ha : raw17728step1 = (fun i j => raw17728step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17728step1 raw17728step0; decide +kernel
      have hl : raw17728step1Labels = raw17728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17728step0 raw17728step0Labels permutation32 permutation3
    mixedMoment B raw17728step1 raw17728step1Labels = mixedMoment B raw17728step2 raw17728step2Labels := by
      have ha : raw17728step2 = raw17728step1 := by apply Matrix.ext; unfold raw17728step2 raw17728step1; decide +kernel
      have hl : raw17728step1Labels = labelEmbedding6 ∘ raw17728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17728step1 raw17728step1Labels raw17728step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw17729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17729 raw17729Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw17729 raw17729Labels = mixedMoment B raw17729step0 raw17729step0Labels := by
      have hz : ∀ j, raw17729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17729step0 = (fun i j => raw17729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17729step0 raw17729; decide +kernel
      have hl : raw17729step0Labels = raw17729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17729 raw17729Labels permutation346 hz
    mixedMoment B raw17729step0 raw17729step0Labels = mixedMoment B raw17729step1 raw17729step1Labels := by
      have ha : raw17729step1 = (fun i j => raw17729step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17729step1 raw17729step0; decide +kernel
      have hl : raw17729step1Labels = raw17729step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17729step0 raw17729step0Labels permutation150 permutation3
    mixedMoment B raw17729step1 raw17729step1Labels = mixedMoment B raw17729step2 raw17729step2Labels := by
      have ha : raw17729step2 = -raw17729step1 := by apply Matrix.ext; change ∀ i j, raw17729step2 i j = -(raw17729step1 i j); unfold raw17729step2 raw17729step1; decide +kernel
      have hl : raw17729step2Labels = raw17729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17729step2 raw17729step2Labels = mixedMoment B raw17729step3 raw17729step3Labels := by
      have ha : raw17729step3 = raw17729step2 := by apply Matrix.ext; unfold raw17729step3 raw17729step2; decide +kernel
      have hl : raw17729step2Labels = labelEmbedding6 ∘ raw17729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17729step2 raw17729step2Labels raw17729step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw17730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17730step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17730 raw17730Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw17730 raw17730Labels = mixedMoment B raw17730step0 raw17730step0Labels := by
      have ha : raw17730step0 = (fun i j => raw17730 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17730step0 raw17730; decide +kernel
      have hl : raw17730step0Labels = raw17730Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17730 raw17730Labels permutation686 permutation3
    mixedMoment B raw17730step0 raw17730step0Labels = mixedMoment B raw17730step1 raw17730step1Labels := by
      have ha : raw17730step1 = -raw17730step0 := by apply Matrix.ext; change ∀ i j, raw17730step1 i j = -(raw17730step0 i j); unfold raw17730step1 raw17730step0; decide +kernel
      have hl : raw17730step1Labels = raw17730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17730step1 raw17730step1Labels = mixedMoment B raw17730step2 raw17730step2Labels := by
      have ha : raw17730step2 = raw17730step1 := by apply Matrix.ext; unfold raw17730step2 raw17730step1; decide +kernel
      have hl : raw17730step1Labels = labelEmbedding6 ∘ raw17730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17730step1 raw17730step1Labels raw17730step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw17731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw17731step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw17731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17731 raw17731Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw17731 raw17731Labels = mixedMoment B raw17731step0 raw17731step0Labels := by
      have hz : ∀ j, raw17731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17731step0 = (fun i j => raw17731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17731step0 raw17731; decide +kernel
      have hl : raw17731step0Labels = raw17731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17731 raw17731Labels permutation346 hz
    mixedMoment B raw17731step0 raw17731step0Labels = mixedMoment B raw17731step1 raw17731step1Labels := by
      have ha : raw17731step1 = (fun i j => raw17731step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17731step1 raw17731step0; decide +kernel
      have hl : raw17731step1Labels = raw17731step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17731step0 raw17731step0Labels permutation149 permutation3
    mixedMoment B raw17731step1 raw17731step1Labels = mixedMoment B raw17731step2 raw17731step2Labels := by
      have ha : raw17731step2 = -raw17731step1 := by apply Matrix.ext; change ∀ i j, raw17731step2 i j = -(raw17731step1 i j); unfold raw17731step2 raw17731step1; decide +kernel
      have hl : raw17731step2Labels = raw17731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17731step2 raw17731step2Labels = mixedMoment B raw17731step3 raw17731step3Labels := by
      have ha : raw17731step3 = raw17731step2 := by apply Matrix.ext; unfold raw17731step3 raw17731step2; decide +kernel
      have hl : raw17731step2Labels = labelEmbedding6 ∘ raw17731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17731step2 raw17731step2Labels raw17731step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw17732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17732step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17732step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17732 raw17732Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw17732 raw17732Labels = mixedMoment B raw17732step0 raw17732step0Labels := by
      have hz : ∀ j, raw17732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17732step0 = (fun i j => raw17732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17732step0 raw17732; decide +kernel
      have hl : raw17732step0Labels = raw17732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17732 raw17732Labels permutation346 hz
    mixedMoment B raw17732step0 raw17732step0Labels = mixedMoment B raw17732step1 raw17732step1Labels := by
      have ha : raw17732step1 = (fun i j => raw17732step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17732step1 raw17732step0; decide +kernel
      have hl : raw17732step1Labels = raw17732step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17732step0 raw17732step0Labels permutation145 permutation3
    mixedMoment B raw17732step1 raw17732step1Labels = mixedMoment B raw17732step2 raw17732step2Labels := by
      have ha : raw17732step2 = -raw17732step1 := by apply Matrix.ext; change ∀ i j, raw17732step2 i j = -(raw17732step1 i j); unfold raw17732step2 raw17732step1; decide +kernel
      have hl : raw17732step2Labels = raw17732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17732step2 raw17732step2Labels = mixedMoment B raw17732step3 raw17732step3Labels := by
      have ha : raw17732step3 = raw17732step2 := by apply Matrix.ext; unfold raw17732step3 raw17732step2; decide +kernel
      have hl : raw17732step2Labels = labelEmbedding6 ∘ raw17732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17732step2 raw17732step2Labels raw17732step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw17733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17733 raw17733Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw17733 raw17733Labels = mixedMoment B raw17733step0 raw17733step0Labels := by
      have hz : ∀ j, raw17733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17733step0 = (fun i j => raw17733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17733step0 raw17733; decide +kernel
      have hl : raw17733step0Labels = raw17733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17733 raw17733Labels permutation346 hz
    mixedMoment B raw17733step0 raw17733step0Labels = mixedMoment B raw17733step1 raw17733step1Labels := by
      have ha : raw17733step1 = (fun i j => raw17733step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17733step1 raw17733step0; decide +kernel
      have hl : raw17733step1Labels = raw17733step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17733step0 raw17733step0Labels permutation126 permutation7
    mixedMoment B raw17733step1 raw17733step1Labels = mixedMoment B raw17733step2 raw17733step2Labels := by
      have ha : raw17733step2 = raw17733step1 := by apply Matrix.ext; unfold raw17733step2 raw17733step1; decide +kernel
      have hl : raw17733step1Labels = labelEmbedding1 ∘ raw17733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17733step1 raw17733step1Labels raw17733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw17734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17734 raw17734Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw17734 raw17734Labels = mixedMoment B raw17734step0 raw17734step0Labels := by
      have ha : raw17734step0 = (fun i j => raw17734 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17734step0 raw17734; decide +kernel
      have hl : raw17734step0Labels = raw17734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17734 raw17734Labels permutation583 permutation7
    mixedMoment B raw17734step0 raw17734step0Labels = mixedMoment B raw17734step1 raw17734step1Labels := by
      have ha : raw17734step1 = raw17734step0 := by apply Matrix.ext; unfold raw17734step1 raw17734step0; decide +kernel
      have hl : raw17734step0Labels = labelEmbedding1 ∘ raw17734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17734step0 raw17734step0Labels raw17734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw17735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17735 raw17735Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw17735 raw17735Labels = mixedMoment B raw17735step0 raw17735step0Labels := by
      have hz : ∀ j, raw17735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17735step0 = (fun i j => raw17735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17735step0 raw17735; decide +kernel
      have hl : raw17735step0Labels = raw17735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17735 raw17735Labels permutation346 hz
    mixedMoment B raw17735step0 raw17735step0Labels = mixedMoment B raw17735step1 raw17735step1Labels := by
      have ha : raw17735step1 = (fun i j => raw17735step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17735step1 raw17735step0; decide +kernel
      have hl : raw17735step1Labels = raw17735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17735step0 raw17735step0Labels permutation122 permutation7
    mixedMoment B raw17735step1 raw17735step1Labels = mixedMoment B raw17735step2 raw17735step2Labels := by
      have ha : raw17735step2 = raw17735step1 := by apply Matrix.ext; unfold raw17735step2 raw17735step1; decide +kernel
      have hl : raw17735step1Labels = labelEmbedding1 ∘ raw17735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17735step1 raw17735step1Labels raw17735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw17736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17736 raw17736Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw17736 raw17736Labels = mixedMoment B raw17736step0 raw17736step0Labels := by
      have hz : ∀ j, raw17736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17736step0 = (fun i j => raw17736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17736step0 raw17736; decide +kernel
      have hl : raw17736step0Labels = raw17736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17736 raw17736Labels permutation346 hz
    mixedMoment B raw17736step0 raw17736step0Labels = mixedMoment B raw17736step1 raw17736step1Labels := by
      have ha : raw17736step1 = (fun i j => raw17736step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17736step1 raw17736step0; decide +kernel
      have hl : raw17736step1Labels = raw17736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17736step0 raw17736step0Labels permutation126 permutation7
    mixedMoment B raw17736step1 raw17736step1Labels = mixedMoment B raw17736step2 raw17736step2Labels := by
      have ha : raw17736step2 = raw17736step1 := by apply Matrix.ext; unfold raw17736step2 raw17736step1; decide +kernel
      have hl : raw17736step1Labels = labelEmbedding1 ∘ raw17736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17736step1 raw17736step1Labels raw17736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw17737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17737 raw17737Labels = mixedMoment B node3985 node3985Labels := by
  calc
    mixedMoment B raw17737 raw17737Labels = mixedMoment B raw17737step0 raw17737step0Labels := by
      have hz : ∀ j, raw17737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17737step0 = (fun i j => raw17737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17737step0 raw17737; decide +kernel
      have hl : raw17737step0Labels = raw17737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17737 raw17737Labels permutation346 hz
    mixedMoment B raw17737step0 raw17737step0Labels = mixedMoment B raw17737step1 raw17737step1Labels := by
      have ha : raw17737step1 = (fun i j => raw17737step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17737step1 raw17737step0; decide +kernel
      have hl : raw17737step1Labels = raw17737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17737step0 raw17737step0Labels permutation126 permutation7
    mixedMoment B raw17737step1 raw17737step1Labels = mixedMoment B raw17737step2 raw17737step2Labels := by
      have ha : raw17737step2 = raw17737step1 := by apply Matrix.ext; unfold raw17737step2 raw17737step1; decide +kernel
      have hl : raw17737step1Labels = labelEmbedding1 ∘ raw17737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17737step1 raw17737step1Labels raw17737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3985 node3985Labels := by rfl

def raw17738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17738 raw17738Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw17738 raw17738Labels = mixedMoment B raw17738step0 raw17738step0Labels := by
      have hz : ∀ j, raw17738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17738step0 = (fun i j => raw17738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17738step0 raw17738; decide +kernel
      have hl : raw17738step0Labels = raw17738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17738 raw17738Labels permutation346 hz
    mixedMoment B raw17738step0 raw17738step0Labels = mixedMoment B raw17738step1 raw17738step1Labels := by
      have ha : raw17738step1 = (fun i j => raw17738step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17738step1 raw17738step0; decide +kernel
      have hl : raw17738step1Labels = raw17738step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17738step0 raw17738step0Labels permutation44 permutation5
    mixedMoment B raw17738step1 raw17738step1Labels = mixedMoment B raw17738step2 raw17738step2Labels := by
      have ha : raw17738step2 = -raw17738step1 := by apply Matrix.ext; change ∀ i j, raw17738step2 i j = -(raw17738step1 i j); unfold raw17738step2 raw17738step1; decide +kernel
      have hl : raw17738step2Labels = raw17738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17738step2 raw17738step2Labels = mixedMoment B raw17738step3 raw17738step3Labels := by
      have ha : raw17738step3 = raw17738step2 := by apply Matrix.ext; unfold raw17738step3 raw17738step2; decide +kernel
      have hl : raw17738step2Labels = labelEmbedding1 ∘ raw17738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17738step2 raw17738step2Labels raw17738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw17739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17739 raw17739Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw17739 raw17739Labels = mixedMoment B raw17739step0 raw17739step0Labels := by
      have ha : raw17739step0 = (fun i j => raw17739 (permutation582 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17739step0 raw17739; decide +kernel
      have hl : raw17739step0Labels = raw17739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17739 raw17739Labels permutation582 permutation7
    mixedMoment B raw17739step0 raw17739step0Labels = mixedMoment B raw17739step1 raw17739step1Labels := by
      have ha : raw17739step1 = raw17739step0 := by apply Matrix.ext; unfold raw17739step1 raw17739step0; decide +kernel
      have hl : raw17739step0Labels = labelEmbedding1 ∘ raw17739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17739step0 raw17739step0Labels raw17739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw17740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17740 raw17740Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw17740 raw17740Labels = mixedMoment B raw17740step0 raw17740step0Labels := by
      have hz : ∀ j, raw17740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17740step0 = (fun i j => raw17740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17740step0 raw17740; decide +kernel
      have hl : raw17740step0Labels = raw17740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17740 raw17740Labels permutation346 hz
    mixedMoment B raw17740step0 raw17740step0Labels = mixedMoment B raw17740step1 raw17740step1Labels := by
      have ha : raw17740step1 = (fun i j => raw17740step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17740step1 raw17740step0; decide +kernel
      have hl : raw17740step1Labels = raw17740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17740step0 raw17740step0Labels permutation125 permutation7
    mixedMoment B raw17740step1 raw17740step1Labels = mixedMoment B raw17740step2 raw17740step2Labels := by
      have ha : raw17740step2 = raw17740step1 := by apply Matrix.ext; unfold raw17740step2 raw17740step1; decide +kernel
      have hl : raw17740step1Labels = labelEmbedding1 ∘ raw17740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17740step1 raw17740step1Labels raw17740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw17741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17741 raw17741Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw17741 raw17741Labels = mixedMoment B raw17741step0 raw17741step0Labels := by
      have hz : ∀ j, raw17741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17741step0 = (fun i j => raw17741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17741step0 raw17741; decide +kernel
      have hl : raw17741step0Labels = raw17741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17741 raw17741Labels permutation346 hz
    mixedMoment B raw17741step0 raw17741step0Labels = mixedMoment B raw17741step1 raw17741step1Labels := by
      have ha : raw17741step1 = (fun i j => raw17741step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17741step1 raw17741step0; decide +kernel
      have hl : raw17741step1Labels = raw17741step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17741step0 raw17741step0Labels permutation104 permutation5
    mixedMoment B raw17741step1 raw17741step1Labels = mixedMoment B raw17741step2 raw17741step2Labels := by
      have ha : raw17741step2 = -raw17741step1 := by apply Matrix.ext; change ∀ i j, raw17741step2 i j = -(raw17741step1 i j); unfold raw17741step2 raw17741step1; decide +kernel
      have hl : raw17741step2Labels = raw17741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17741step2 raw17741step2Labels = mixedMoment B raw17741step3 raw17741step3Labels := by
      have ha : raw17741step3 = raw17741step2 := by apply Matrix.ext; unfold raw17741step3 raw17741step2; decide +kernel
      have hl : raw17741step2Labels = labelEmbedding1 ∘ raw17741step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17741step2 raw17741step2Labels raw17741step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw17742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17742 raw17742Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw17742 raw17742Labels = mixedMoment B raw17742step0 raw17742step0Labels := by
      have hz : ∀ j, raw17742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17742step0 = (fun i j => raw17742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17742step0 raw17742; decide +kernel
      have hl : raw17742step0Labels = raw17742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17742 raw17742Labels permutation346 hz
    mixedMoment B raw17742step0 raw17742step0Labels = mixedMoment B raw17742step1 raw17742step1Labels := by
      have ha : raw17742step1 = (fun i j => raw17742step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17742step1 raw17742step0; decide +kernel
      have hl : raw17742step1Labels = raw17742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17742step0 raw17742step0Labels permutation125 permutation7
    mixedMoment B raw17742step1 raw17742step1Labels = mixedMoment B raw17742step2 raw17742step2Labels := by
      have ha : raw17742step2 = raw17742step1 := by apply Matrix.ext; unfold raw17742step2 raw17742step1; decide +kernel
      have hl : raw17742step1Labels = labelEmbedding1 ∘ raw17742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17742step1 raw17742step1Labels raw17742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw17743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17743 raw17743Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw17743 raw17743Labels = mixedMoment B raw17743step0 raw17743step0Labels := by
      have ha : raw17743step0 = (fun i j => raw17743 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17743step0 raw17743; decide +kernel
      have hl : raw17743step0Labels = raw17743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17743 raw17743Labels permutation226 permutation5
    mixedMoment B raw17743step0 raw17743step0Labels = mixedMoment B raw17743step1 raw17743step1Labels := by
      have ha : raw17743step1 = -raw17743step0 := by apply Matrix.ext; change ∀ i j, raw17743step1 i j = -(raw17743step0 i j); unfold raw17743step1 raw17743step0; decide +kernel
      have hl : raw17743step1Labels = raw17743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17743step1 raw17743step1Labels = mixedMoment B raw17743step2 raw17743step2Labels := by
      have ha : raw17743step2 = raw17743step1 := by apply Matrix.ext; unfold raw17743step2 raw17743step1; decide +kernel
      have hl : raw17743step1Labels = labelEmbedding1 ∘ raw17743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17743step1 raw17743step1Labels raw17743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw17744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17744 raw17744Labels = mixedMoment B node3951 node3951Labels := by
  calc
    mixedMoment B raw17744 raw17744Labels = mixedMoment B raw17744step0 raw17744step0Labels := by
      have ha : raw17744step0 = (fun i j => raw17744 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17744step0 raw17744; decide +kernel
      have hl : raw17744step0Labels = raw17744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17744 raw17744Labels permutation583 permutation7
    mixedMoment B raw17744step0 raw17744step0Labels = mixedMoment B raw17744step1 raw17744step1Labels := by
      have ha : raw17744step1 = raw17744step0 := by apply Matrix.ext; unfold raw17744step1 raw17744step0; decide +kernel
      have hl : raw17744step0Labels = labelEmbedding1 ∘ raw17744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17744step0 raw17744step0Labels raw17744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3951 node3951Labels := by rfl

def raw17745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17745 raw17745Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw17745 raw17745Labels = mixedMoment B raw17745step0 raw17745step0Labels := by
      have ha : raw17745step0 = (fun i j => raw17745 (permutation582 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17745step0 raw17745; decide +kernel
      have hl : raw17745step0Labels = raw17745Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17745 raw17745Labels permutation582 permutation7
    mixedMoment B raw17745step0 raw17745step0Labels = mixedMoment B raw17745step1 raw17745step1Labels := by
      have ha : raw17745step1 = raw17745step0 := by apply Matrix.ext; unfold raw17745step1 raw17745step0; decide +kernel
      have hl : raw17745step0Labels = labelEmbedding1 ∘ raw17745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17745step0 raw17745step0Labels raw17745step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw17746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17746 raw17746Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw17746 raw17746Labels = mixedMoment B raw17746step0 raw17746step0Labels := by
      have ha : raw17746step0 = (fun i j => raw17746 (permutation522 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17746step0 raw17746; decide +kernel
      have hl : raw17746step0Labels = raw17746Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17746 raw17746Labels permutation522 permutation5
    mixedMoment B raw17746step0 raw17746step0Labels = mixedMoment B raw17746step1 raw17746step1Labels := by
      have ha : raw17746step1 = -raw17746step0 := by apply Matrix.ext; change ∀ i j, raw17746step1 i j = -(raw17746step0 i j); unfold raw17746step1 raw17746step0; decide +kernel
      have hl : raw17746step1Labels = raw17746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17746step1 raw17746step1Labels = mixedMoment B raw17746step2 raw17746step2Labels := by
      have ha : raw17746step2 = raw17746step1 := by apply Matrix.ext; unfold raw17746step2 raw17746step1; decide +kernel
      have hl : raw17746step1Labels = labelEmbedding1 ∘ raw17746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17746step1 raw17746step1Labels raw17746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw17747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17747 raw17747Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17747 raw17747Labels = mixedMoment B raw17747step0 raw17747step0Labels := by
      have ha : raw17747step0 = (fun i j => raw17747 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17747step0 raw17747; decide +kernel
      have hl : raw17747step0Labels = raw17747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17747 raw17747Labels permutation584 permutation7
    mixedMoment B raw17747step0 raw17747step0Labels = mixedMoment B raw17747step1 raw17747step1Labels := by
      have ha : raw17747step1 = raw17747step0 := by apply Matrix.ext; unfold raw17747step1 raw17747step0; decide +kernel
      have hl : raw17747step0Labels = labelEmbedding1 ∘ raw17747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17747step0 raw17747step0Labels raw17747step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17748 raw17748Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw17748 raw17748Labels = mixedMoment B raw17748step0 raw17748step0Labels := by
      have hz : ∀ j, raw17748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17748step0 = (fun i j => raw17748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17748step0 raw17748; decide +kernel
      have hl : raw17748step0Labels = raw17748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17748 raw17748Labels permutation346 hz
    mixedMoment B raw17748step0 raw17748step0Labels = mixedMoment B raw17748step1 raw17748step1Labels := by
      have ha : raw17748step1 = (fun i j => raw17748step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17748step1 raw17748step0; decide +kernel
      have hl : raw17748step1Labels = raw17748step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17748step0 raw17748step0Labels permutation45 permutation5
    mixedMoment B raw17748step1 raw17748step1Labels = mixedMoment B raw17748step2 raw17748step2Labels := by
      have ha : raw17748step2 = -raw17748step1 := by apply Matrix.ext; change ∀ i j, raw17748step2 i j = -(raw17748step1 i j); unfold raw17748step2 raw17748step1; decide +kernel
      have hl : raw17748step2Labels = raw17748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17748step2 raw17748step2Labels = mixedMoment B raw17748step3 raw17748step3Labels := by
      have ha : raw17748step3 = raw17748step2 := by apply Matrix.ext; unfold raw17748step3 raw17748step2; decide +kernel
      have hl : raw17748step2Labels = labelEmbedding1 ∘ raw17748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17748step2 raw17748step2Labels raw17748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw17749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17749 raw17749Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw17749 raw17749Labels = mixedMoment B raw17749step0 raw17749step0Labels := by
      have hz : ∀ j, raw17749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17749step0 = (fun i j => raw17749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17749step0 raw17749; decide +kernel
      have hl : raw17749step0Labels = raw17749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17749 raw17749Labels permutation346 hz
    mixedMoment B raw17749step0 raw17749step0Labels = mixedMoment B raw17749step1 raw17749step1Labels := by
      have ha : raw17749step1 = (fun i j => raw17749step0 (permutation102 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17749step1 raw17749step0; decide +kernel
      have hl : raw17749step1Labels = raw17749step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17749step0 raw17749step0Labels permutation102 permutation5
    mixedMoment B raw17749step1 raw17749step1Labels = mixedMoment B raw17749step2 raw17749step2Labels := by
      have ha : raw17749step2 = raw17749step1 := by apply Matrix.ext; unfold raw17749step2 raw17749step1; decide +kernel
      have hl : raw17749step1Labels = labelEmbedding1 ∘ raw17749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17749step1 raw17749step1Labels raw17749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

def raw17750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17750 raw17750Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw17750 raw17750Labels = mixedMoment B raw17750step0 raw17750step0Labels := by
      have ha : raw17750step0 = (fun i j => raw17750 (permutation511 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17750step0 raw17750; decide +kernel
      have hl : raw17750step0Labels = raw17750Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17750 raw17750Labels permutation511 permutation5
    mixedMoment B raw17750step0 raw17750step0Labels = mixedMoment B raw17750step1 raw17750step1Labels := by
      have ha : raw17750step1 = raw17750step0 := by apply Matrix.ext; unfold raw17750step1 raw17750step0; decide +kernel
      have hl : raw17750step0Labels = labelEmbedding1 ∘ raw17750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17750step0 raw17750step0Labels raw17750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw17751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17751 raw17751Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw17751 raw17751Labels = mixedMoment B raw17751step0 raw17751step0Labels := by
      have hz : ∀ j, raw17751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17751step0 = (fun i j => raw17751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17751step0 raw17751; decide +kernel
      have hl : raw17751step0Labels = raw17751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17751 raw17751Labels permutation346 hz
    mixedMoment B raw17751step0 raw17751step0Labels = mixedMoment B raw17751step1 raw17751step1Labels := by
      have ha : raw17751step1 = (fun i j => raw17751step0 (permutation100 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17751step1 raw17751step0; decide +kernel
      have hl : raw17751step1Labels = raw17751step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17751step0 raw17751step0Labels permutation100 permutation5
    mixedMoment B raw17751step1 raw17751step1Labels = mixedMoment B raw17751step2 raw17751step2Labels := by
      have ha : raw17751step2 = raw17751step1 := by apply Matrix.ext; unfold raw17751step2 raw17751step1; decide +kernel
      have hl : raw17751step1Labels = labelEmbedding1 ∘ raw17751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17751step1 raw17751step1Labels raw17751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw17752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw17752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17752 raw17752Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw17752 raw17752Labels = mixedMoment B raw17752step0 raw17752step0Labels := by
      have hz : ∀ j, raw17752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17752step0 = (fun i j => raw17752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17752step0 raw17752; decide +kernel
      have hl : raw17752step0Labels = raw17752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17752 raw17752Labels permutation346 hz
    mixedMoment B raw17752step0 raw17752step0Labels = mixedMoment B raw17752step1 raw17752step1Labels := by
      have ha : raw17752step1 = (fun i j => raw17752step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17752step1 raw17752step0; decide +kernel
      have hl : raw17752step1Labels = raw17752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17752step0 raw17752step0Labels permutation127 permutation7
    mixedMoment B raw17752step1 raw17752step1Labels = mixedMoment B raw17752step2 raw17752step2Labels := by
      have ha : raw17752step2 = raw17752step1 := by apply Matrix.ext; unfold raw17752step2 raw17752step1; decide +kernel
      have hl : raw17752step1Labels = labelEmbedding1 ∘ raw17752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17752step1 raw17752step1Labels raw17752step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw17753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw17753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw17753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17753 raw17753Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw17753 raw17753Labels = mixedMoment B raw17753step0 raw17753step0Labels := by
      have hz : ∀ j, raw17753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17753step0 = (fun i j => raw17753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17753step0 raw17753; decide +kernel
      have hl : raw17753step0Labels = raw17753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17753 raw17753Labels permutation346 hz
    mixedMoment B raw17753step0 raw17753step0Labels = mixedMoment B raw17753step1 raw17753step1Labels := by
      have ha : raw17753step1 = (fun i j => raw17753step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17753step1 raw17753step0; decide +kernel
      have hl : raw17753step1Labels = raw17753step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17753step0 raw17753step0Labels permutation34 permutation5
    mixedMoment B raw17753step1 raw17753step1Labels = mixedMoment B raw17753step2 raw17753step2Labels := by
      have ha : raw17753step2 = -raw17753step1 := by apply Matrix.ext; change ∀ i j, raw17753step2 i j = -(raw17753step1 i j); unfold raw17753step2 raw17753step1; decide +kernel
      have hl : raw17753step2Labels = raw17753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17753step2 raw17753step2Labels = mixedMoment B raw17753step3 raw17753step3Labels := by
      have ha : raw17753step3 = raw17753step2 := by apply Matrix.ext; unfold raw17753step3 raw17753step2; decide +kernel
      have hl : raw17753step2Labels = labelEmbedding1 ∘ raw17753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17753step2 raw17753step2Labels raw17753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw17754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17754 raw17754Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw17754 raw17754Labels = mixedMoment B raw17754step0 raw17754step0Labels := by
      have hz : ∀ j, raw17754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17754step0 = (fun i j => raw17754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17754step0 raw17754; decide +kernel
      have hl : raw17754step0Labels = raw17754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17754 raw17754Labels permutation346 hz
    mixedMoment B raw17754step0 raw17754step0Labels = mixedMoment B raw17754step1 raw17754step1Labels := by
      have ha : raw17754step1 = (fun i j => raw17754step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17754step1 raw17754step0; decide +kernel
      have hl : raw17754step1Labels = raw17754step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17754step0 raw17754step0Labels permutation126 permutation7
    mixedMoment B raw17754step1 raw17754step1Labels = mixedMoment B raw17754step2 raw17754step2Labels := by
      have ha : raw17754step2 = raw17754step1 := by apply Matrix.ext; unfold raw17754step2 raw17754step1; decide +kernel
      have hl : raw17754step1Labels = labelEmbedding1 ∘ raw17754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17754step1 raw17754step1Labels raw17754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw17755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17755 raw17755Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw17755 raw17755Labels = mixedMoment B raw17755step0 raw17755step0Labels := by
      have ha : raw17755step0 = (fun i j => raw17755 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17755step0 raw17755; decide +kernel
      have hl : raw17755step0Labels = raw17755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17755 raw17755Labels permutation584 permutation7
    mixedMoment B raw17755step0 raw17755step0Labels = mixedMoment B raw17755step1 raw17755step1Labels := by
      have ha : raw17755step1 = raw17755step0 := by apply Matrix.ext; unfold raw17755step1 raw17755step0; decide +kernel
      have hl : raw17755step0Labels = labelEmbedding1 ∘ raw17755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17755step0 raw17755step0Labels raw17755step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw17756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw17756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17756 raw17756Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw17756 raw17756Labels = mixedMoment B raw17756step0 raw17756step0Labels := by
      have hz : ∀ j, raw17756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17756step0 = (fun i j => raw17756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17756step0 raw17756; decide +kernel
      have hl : raw17756step0Labels = raw17756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17756 raw17756Labels permutation346 hz
    mixedMoment B raw17756step0 raw17756step0Labels = mixedMoment B raw17756step1 raw17756step1Labels := by
      have ha : raw17756step1 = (fun i j => raw17756step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17756step1 raw17756step0; decide +kernel
      have hl : raw17756step1Labels = raw17756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17756step0 raw17756step0Labels permutation125 permutation7
    mixedMoment B raw17756step1 raw17756step1Labels = mixedMoment B raw17756step2 raw17756step2Labels := by
      have ha : raw17756step2 = raw17756step1 := by apply Matrix.ext; unfold raw17756step2 raw17756step1; decide +kernel
      have hl : raw17756step1Labels = labelEmbedding1 ∘ raw17756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17756step1 raw17756step1Labels raw17756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

def raw17757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw17757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17757 raw17757Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw17757 raw17757Labels = mixedMoment B raw17757step0 raw17757step0Labels := by
      have hz : ∀ j, raw17757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17757step0 = (fun i j => raw17757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17757step0 raw17757; decide +kernel
      have hl : raw17757step0Labels = raw17757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17757 raw17757Labels permutation346 hz
    mixedMoment B raw17757step0 raw17757step0Labels = mixedMoment B raw17757step1 raw17757step1Labels := by
      have ha : raw17757step1 = (fun i j => raw17757step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17757step1 raw17757step0; decide +kernel
      have hl : raw17757step1Labels = raw17757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17757step0 raw17757step0Labels permutation127 permutation7
    mixedMoment B raw17757step1 raw17757step1Labels = mixedMoment B raw17757step2 raw17757step2Labels := by
      have ha : raw17757step2 = raw17757step1 := by apply Matrix.ext; unfold raw17757step2 raw17757step1; decide +kernel
      have hl : raw17757step1Labels = labelEmbedding1 ∘ raw17757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17757step1 raw17757step1Labels raw17757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw17758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw17758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17758 raw17758Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw17758 raw17758Labels = mixedMoment B raw17758step0 raw17758step0Labels := by
      have hz : ∀ j, raw17758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17758step0 = (fun i j => raw17758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17758step0 raw17758; decide +kernel
      have hl : raw17758step0Labels = raw17758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17758 raw17758Labels permutation346 hz
    mixedMoment B raw17758step0 raw17758step0Labels = mixedMoment B raw17758step1 raw17758step1Labels := by
      have ha : raw17758step1 = (fun i j => raw17758step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17758step1 raw17758step0; decide +kernel
      have hl : raw17758step1Labels = raw17758step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17758step0 raw17758step0Labels permutation143 permutation5
    mixedMoment B raw17758step1 raw17758step1Labels = mixedMoment B raw17758step2 raw17758step2Labels := by
      have ha : raw17758step2 = raw17758step1 := by apply Matrix.ext; unfold raw17758step2 raw17758step1; decide +kernel
      have hl : raw17758step1Labels = labelEmbedding1 ∘ raw17758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17758step1 raw17758step1Labels raw17758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw17759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17759 raw17759Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw17759 raw17759Labels = mixedMoment B raw17759step0 raw17759step0Labels := by
      have hz : ∀ j, raw17759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17759step0 = (fun i j => raw17759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17759step0 raw17759; decide +kernel
      have hl : raw17759step0Labels = raw17759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17759 raw17759Labels permutation346 hz
    mixedMoment B raw17759step0 raw17759step0Labels = mixedMoment B raw17759step1 raw17759step1Labels := by
      have ha : raw17759step1 = (fun i j => raw17759step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17759step1 raw17759step0; decide +kernel
      have hl : raw17759step1Labels = raw17759step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17759step0 raw17759step0Labels permutation144 permutation5
    mixedMoment B raw17759step1 raw17759step1Labels = mixedMoment B raw17759step2 raw17759step2Labels := by
      have ha : raw17759step2 = raw17759step1 := by apply Matrix.ext; unfold raw17759step2 raw17759step1; decide +kernel
      have hl : raw17759step1Labels = labelEmbedding1 ∘ raw17759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17759step1 raw17759step1Labels raw17759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw17760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17760 raw17760Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw17760 raw17760Labels = mixedMoment B raw17760step0 raw17760step0Labels := by
      have ha : raw17760step0 = (fun i j => raw17760 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17760step0 raw17760; decide +kernel
      have hl : raw17760step0Labels = raw17760Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17760 raw17760Labels permutation654 permutation5
    mixedMoment B raw17760step0 raw17760step0Labels = mixedMoment B raw17760step1 raw17760step1Labels := by
      have ha : raw17760step1 = raw17760step0 := by apply Matrix.ext; unfold raw17760step1 raw17760step0; decide +kernel
      have hl : raw17760step0Labels = labelEmbedding1 ∘ raw17760step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17760step0 raw17760step0Labels raw17760step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw17761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17761 raw17761Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw17761 raw17761Labels = mixedMoment B raw17761step0 raw17761step0Labels := by
      have hz : ∀ j, raw17761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17761step0 = (fun i j => raw17761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17761step0 raw17761; decide +kernel
      have hl : raw17761step0Labels = raw17761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17761 raw17761Labels permutation346 hz
    mixedMoment B raw17761step0 raw17761step0Labels = mixedMoment B raw17761step1 raw17761step1Labels := by
      have ha : raw17761step1 = (fun i j => raw17761step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17761step1 raw17761step0; decide +kernel
      have hl : raw17761step1Labels = raw17761step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17761step0 raw17761step0Labels permutation137 permutation5
    mixedMoment B raw17761step1 raw17761step1Labels = mixedMoment B raw17761step2 raw17761step2Labels := by
      have ha : raw17761step2 = raw17761step1 := by apply Matrix.ext; unfold raw17761step2 raw17761step1; decide +kernel
      have hl : raw17761step1Labels = labelEmbedding1 ∘ raw17761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17761step1 raw17761step1Labels raw17761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw17762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw17762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17762 raw17762Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw17762 raw17762Labels = mixedMoment B raw17762step0 raw17762step0Labels := by
      have hz : ∀ j, raw17762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17762step0 = (fun i j => raw17762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17762step0 raw17762; decide +kernel
      have hl : raw17762step0Labels = raw17762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17762 raw17762Labels permutation346 hz
    mixedMoment B raw17762step0 raw17762step0Labels = mixedMoment B raw17762step1 raw17762step1Labels := by
      have ha : raw17762step1 = (fun i j => raw17762step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17762step1 raw17762step0; decide +kernel
      have hl : raw17762step1Labels = raw17762step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17762step0 raw17762step0Labels permutation142 permutation5
    mixedMoment B raw17762step1 raw17762step1Labels = mixedMoment B raw17762step2 raw17762step2Labels := by
      have ha : raw17762step2 = raw17762step1 := by apply Matrix.ext; unfold raw17762step2 raw17762step1; decide +kernel
      have hl : raw17762step1Labels = labelEmbedding1 ∘ raw17762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17762step1 raw17762step1Labels raw17762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw17763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17763 raw17763Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17763 raw17763Labels = mixedMoment B raw17763step0 raw17763step0Labels := by
      have hz : ∀ j, raw17763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17763step0 = (fun i j => raw17763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17763step0 raw17763; decide +kernel
      have hl : raw17763step0Labels = raw17763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17763 raw17763Labels permutation346 hz
    mixedMoment B raw17763step0 raw17763step0Labels = mixedMoment B raw17763step1 raw17763step1Labels := by
      have ha : raw17763step1 = (fun i j => raw17763step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17763step1 raw17763step0; decide +kernel
      have hl : raw17763step1Labels = raw17763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17763step0 raw17763step0Labels permutation56 permutation3
    mixedMoment B raw17763step1 raw17763step1Labels = mixedMoment B raw17763step2 raw17763step2Labels := by
      have ha : raw17763step2 = raw17763step1 := by apply Matrix.ext; unfold raw17763step2 raw17763step1; decide +kernel
      have hl : raw17763step1Labels = labelEmbedding6 ∘ raw17763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17763step1 raw17763step1Labels raw17763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw17764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17764 raw17764Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw17764 raw17764Labels = mixedMoment B raw17764step0 raw17764step0Labels := by
      have ha : raw17764step0 = (fun i j => raw17764 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17764step0 raw17764; decide +kernel
      have hl : raw17764step0Labels = raw17764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17764 raw17764Labels permutation683 permutation3
    mixedMoment B raw17764step0 raw17764step0Labels = mixedMoment B raw17764step1 raw17764step1Labels := by
      have ha : raw17764step1 = -raw17764step0 := by apply Matrix.ext; change ∀ i j, raw17764step1 i j = -(raw17764step0 i j); unfold raw17764step1 raw17764step0; decide +kernel
      have hl : raw17764step1Labels = raw17764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17764step1 raw17764step1Labels = mixedMoment B raw17764step2 raw17764step2Labels := by
      have ha : raw17764step2 = raw17764step1 := by apply Matrix.ext; unfold raw17764step2 raw17764step1; decide +kernel
      have hl : raw17764step1Labels = labelEmbedding6 ∘ raw17764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17764step1 raw17764step1Labels raw17764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw17765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17765 raw17765Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17765 raw17765Labels = mixedMoment B raw17765step0 raw17765step0Labels := by
      have hz : ∀ j, raw17765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17765step0 = (fun i j => raw17765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17765step0 raw17765; decide +kernel
      have hl : raw17765step0Labels = raw17765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17765 raw17765Labels permutation346 hz
    mixedMoment B raw17765step0 raw17765step0Labels = mixedMoment B raw17765step1 raw17765step1Labels := by
      have ha : raw17765step1 = (fun i j => raw17765step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17765step1 raw17765step0; decide +kernel
      have hl : raw17765step1Labels = raw17765step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17765step0 raw17765step0Labels permutation122 permutation5
    mixedMoment B raw17765step1 raw17765step1Labels = mixedMoment B raw17765step2 raw17765step2Labels := by
      have ha : raw17765step2 = raw17765step1 := by apply Matrix.ext; unfold raw17765step2 raw17765step1; decide +kernel
      have hl : raw17765step1Labels = labelEmbedding8 ∘ raw17765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17765step1 raw17765step1Labels raw17765step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17766 raw17766Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17766 raw17766Labels = mixedMoment B raw17766step0 raw17766step0Labels := by
      have hz : ∀ j, raw17766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17766step0 = (fun i j => raw17766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17766step0 raw17766; decide +kernel
      have hl : raw17766step0Labels = raw17766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17766 raw17766Labels permutation346 hz
    mixedMoment B raw17766step0 raw17766step0Labels = mixedMoment B raw17766step1 raw17766step1Labels := by
      have ha : raw17766step1 = (fun i j => raw17766step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17766step1 raw17766step0; decide +kernel
      have hl : raw17766step1Labels = raw17766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17766step0 raw17766step0Labels permutation145 permutation2
    mixedMoment B raw17766step1 raw17766step1Labels = mixedMoment B raw17766step2 raw17766step2Labels := by
      have ha : raw17766step2 = -raw17766step1 := by apply Matrix.ext; change ∀ i j, raw17766step2 i j = -(raw17766step1 i j); unfold raw17766step2 raw17766step1; decide +kernel
      have hl : raw17766step2Labels = raw17766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw17767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17767 raw17767Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17767 raw17767Labels = mixedMoment B raw17767step0 raw17767step0Labels := by
      have hz : ∀ j, raw17767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17767step0 = (fun i j => raw17767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17767step0 raw17767; decide +kernel
      have hl : raw17767step0Labels = raw17767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17767 raw17767Labels permutation346 hz
    mixedMoment B raw17767step0 raw17767step0Labels = mixedMoment B raw17767step1 raw17767step1Labels := by
      have ha : raw17767step1 = (fun i j => raw17767step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17767step1 raw17767step0; decide +kernel
      have hl : raw17767step1Labels = raw17767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17767step0 raw17767step0Labels permutation108 permutation4
    mixedMoment B raw17767step1 raw17767step1Labels = mixedMoment B raw17767step2 raw17767step2Labels := by
      have ha : raw17767step2 = raw17767step1 := by apply Matrix.ext; unfold raw17767step2 raw17767step1; decide +kernel
      have hl : raw17767step1Labels = labelEmbedding7 ∘ raw17767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17767step1 raw17767step1Labels raw17767step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw17768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17768step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17768 raw17768Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw17768 raw17768Labels = mixedMoment B raw17768step0 raw17768step0Labels := by
      have hz : ∀ j, raw17768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17768step0 = (fun i j => raw17768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17768step0 raw17768; decide +kernel
      have hl : raw17768step0Labels = raw17768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17768 raw17768Labels permutation346 hz
    mixedMoment B raw17768step0 raw17768step0Labels = mixedMoment B raw17768step1 raw17768step1Labels := by
      have hz : ∀ j, raw17768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17768step1 = (fun i j => raw17768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17768step1 raw17768step0; decide +kernel
      have hl : raw17768step1Labels = raw17768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17768step0 raw17768step0Labels permutation56 hz
    mixedMoment B raw17768step1 raw17768step1Labels = mixedMoment B raw17768step2 raw17768step2Labels := by
      have ha : raw17768step2 = (fun i j => raw17768step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17768step2 raw17768step1; decide +kernel
      have hl : raw17768step2Labels = raw17768step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17768step1 raw17768step1Labels permutation8 permutation3
    mixedMoment B raw17768step2 raw17768step2Labels = mixedMoment B raw17768step3 raw17768step3Labels := by
      have ha : raw17768step3 = raw17768step2 := by apply Matrix.ext; unfold raw17768step3 raw17768step2; decide +kernel
      have hl : raw17768step2Labels = labelEmbedding6 ∘ raw17768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17768step2 raw17768step2Labels raw17768step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw17769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17769step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17769 raw17769Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17769 raw17769Labels = mixedMoment B raw17769step0 raw17769step0Labels := by
      have ha : raw17769step0 = (fun i j => raw17769 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17769step0 raw17769; decide +kernel
      have hl : raw17769step0Labels = raw17769Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17769 raw17769Labels permutation271 permutation3
    mixedMoment B raw17769step0 raw17769step0Labels = mixedMoment B raw17769step1 raw17769step1Labels := by
      have ha : raw17769step1 = raw17769step0 := by apply Matrix.ext; unfold raw17769step1 raw17769step0; decide +kernel
      have hl : raw17769step0Labels = labelEmbedding6 ∘ raw17769step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17769step0 raw17769step0Labels raw17769step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17770 raw17770Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw17770 raw17770Labels = mixedMoment B raw17770step0 raw17770step0Labels := by
      have ha : raw17770step0 = (fun i j => raw17770 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17770step0 raw17770; decide +kernel
      have hl : raw17770step0Labels = raw17770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17770 raw17770Labels permutation200 permutation3
    mixedMoment B raw17770step0 raw17770step0Labels = mixedMoment B raw17770step1 raw17770step1Labels := by
      have ha : raw17770step1 = raw17770step0 := by apply Matrix.ext; unfold raw17770step1 raw17770step0; decide +kernel
      have hl : raw17770step0Labels = labelEmbedding6 ∘ raw17770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17770step0 raw17770step0Labels raw17770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw17771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17771 raw17771Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17771 raw17771Labels = mixedMoment B raw17771step0 raw17771step0Labels := by
      have ha : raw17771step0 = (fun i j => raw17771 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17771step0 raw17771; decide +kernel
      have hl : raw17771step0Labels = raw17771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17771 raw17771Labels permutation160 permutation3
    mixedMoment B raw17771step0 raw17771step0Labels = mixedMoment B raw17771step1 raw17771step1Labels := by
      have ha : raw17771step1 = raw17771step0 := by apply Matrix.ext; unfold raw17771step1 raw17771step0; decide +kernel
      have hl : raw17771step0Labels = labelEmbedding6 ∘ raw17771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17771step0 raw17771step0Labels raw17771step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw17772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17772 raw17772Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17772 raw17772Labels = mixedMoment B raw17772step0 raw17772step0Labels := by
      have ha : raw17772step0 = (fun i j => raw17772 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17772step0 raw17772; decide +kernel
      have hl : raw17772step0Labels = raw17772Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17772 raw17772Labels permutation162 permutation3
    mixedMoment B raw17772step0 raw17772step0Labels = mixedMoment B raw17772step1 raw17772step1Labels := by
      have ha : raw17772step1 = raw17772step0 := by apply Matrix.ext; unfold raw17772step1 raw17772step0; decide +kernel
      have hl : raw17772step0Labels = labelEmbedding6 ∘ raw17772step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17772step0 raw17772step0Labels raw17772step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw17773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17773 raw17773Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17773 raw17773Labels = mixedMoment B raw17773step0 raw17773step0Labels := by
      have hz : ∀ j, raw17773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17773step0 = (fun i j => raw17773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17773step0 raw17773; decide +kernel
      have hl : raw17773step0Labels = raw17773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17773 raw17773Labels permutation346 hz
    mixedMoment B raw17773step0 raw17773step0Labels = mixedMoment B raw17773step1 raw17773step1Labels := by
      have ha : raw17773step1 = (fun i j => raw17773step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17773step1 raw17773step0; decide +kernel
      have hl : raw17773step1Labels = raw17773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17773step0 raw17773step0Labels permutation56 permutation3
    mixedMoment B raw17773step1 raw17773step1Labels = mixedMoment B raw17773step2 raw17773step2Labels := by
      have ha : raw17773step2 = raw17773step1 := by apply Matrix.ext; unfold raw17773step2 raw17773step1; decide +kernel
      have hl : raw17773step1Labels = labelEmbedding6 ∘ raw17773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17773step1 raw17773step1Labels raw17773step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17774 raw17774Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw17774 raw17774Labels = mixedMoment B raw17774step0 raw17774step0Labels := by
      have ha : raw17774step0 = (fun i j => raw17774 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17774step0 raw17774; decide +kernel
      have hl : raw17774step0Labels = raw17774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17774 raw17774Labels permutation686 permutation3
    mixedMoment B raw17774step0 raw17774step0Labels = mixedMoment B raw17774step1 raw17774step1Labels := by
      have ha : raw17774step1 = -raw17774step0 := by apply Matrix.ext; change ∀ i j, raw17774step1 i j = -(raw17774step0 i j); unfold raw17774step1 raw17774step0; decide +kernel
      have hl : raw17774step1Labels = raw17774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17774step1 raw17774step1Labels = mixedMoment B raw17774step2 raw17774step2Labels := by
      have ha : raw17774step2 = raw17774step1 := by apply Matrix.ext; unfold raw17774step2 raw17774step1; decide +kernel
      have hl : raw17774step1Labels = labelEmbedding6 ∘ raw17774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17774step1 raw17774step1Labels raw17774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw17775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17775 raw17775Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17775 raw17775Labels = mixedMoment B raw17775step0 raw17775step0Labels := by
      have hz : ∀ j, raw17775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17775step0 = (fun i j => raw17775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17775step0 raw17775; decide +kernel
      have hl : raw17775step0Labels = raw17775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17775 raw17775Labels permutation346 hz
    mixedMoment B raw17775step0 raw17775step0Labels = mixedMoment B raw17775step1 raw17775step1Labels := by
      have ha : raw17775step1 = (fun i j => raw17775step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17775step1 raw17775step0; decide +kernel
      have hl : raw17775step1Labels = raw17775step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17775step0 raw17775step0Labels permutation145 permutation2
    mixedMoment B raw17775step1 raw17775step1Labels = mixedMoment B raw17775step2 raw17775step2Labels := by
      have ha : raw17775step2 = -raw17775step1 := by apply Matrix.ext; change ∀ i j, raw17775step2 i j = -(raw17775step1 i j); unfold raw17775step2 raw17775step1; decide +kernel
      have hl : raw17775step2Labels = raw17775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17776 raw17776Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17776 raw17776Labels = mixedMoment B raw17776step0 raw17776step0Labels := by
      have hz : ∀ j, raw17776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17776step0 = (fun i j => raw17776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17776step0 raw17776; decide +kernel
      have hl : raw17776step0Labels = raw17776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17776 raw17776Labels permutation346 hz
    mixedMoment B raw17776step0 raw17776step0Labels = mixedMoment B raw17776step1 raw17776step1Labels := by
      have ha : raw17776step1 = (fun i j => raw17776step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17776step1 raw17776step0; decide +kernel
      have hl : raw17776step1Labels = raw17776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17776step0 raw17776step0Labels permutation33 permutation3
    mixedMoment B raw17776step1 raw17776step1Labels = mixedMoment B raw17776step2 raw17776step2Labels := by
      have ha : raw17776step2 = raw17776step1 := by apply Matrix.ext; unfold raw17776step2 raw17776step1; decide +kernel
      have hl : raw17776step1Labels = labelEmbedding6 ∘ raw17776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17776step1 raw17776step1Labels raw17776step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw17777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17777 raw17777Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw17777 raw17777Labels = mixedMoment B raw17777step0 raw17777step0Labels := by
      have hz : ∀ j, raw17777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17777step0 = (fun i j => raw17777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17777step0 raw17777; decide +kernel
      have hl : raw17777step0Labels = raw17777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17777 raw17777Labels permutation346 hz
    mixedMoment B raw17777step0 raw17777step0Labels = mixedMoment B raw17777step1 raw17777step1Labels := by
      have ha : raw17777step1 = (fun i j => raw17777step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17777step1 raw17777step0; decide +kernel
      have hl : raw17777step1Labels = raw17777step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17777step0 raw17777step0Labels permutation126 permutation5
    mixedMoment B raw17777step1 raw17777step1Labels = mixedMoment B raw17777step2 raw17777step2Labels := by
      have ha : raw17777step2 = raw17777step1 := by apply Matrix.ext; unfold raw17777step2 raw17777step1; decide +kernel
      have hl : raw17777step1Labels = labelEmbedding8 ∘ raw17777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17777step1 raw17777step1Labels raw17777step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw17778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17778 raw17778Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw17778 raw17778Labels = mixedMoment B raw17778step0 raw17778step0Labels := by
      have ha : raw17778step0 = (fun i j => raw17778 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17778step0 raw17778; decide +kernel
      have hl : raw17778step0Labels = raw17778Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17778 raw17778Labels permutation587 permutation5
    mixedMoment B raw17778step0 raw17778step0Labels = mixedMoment B raw17778step1 raw17778step1Labels := by
      have ha : raw17778step1 = raw17778step0 := by apply Matrix.ext; unfold raw17778step1 raw17778step0; decide +kernel
      have hl : raw17778step0Labels = labelEmbedding8 ∘ raw17778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17778step0 raw17778step0Labels raw17778step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw17779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17779 raw17779Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw17779 raw17779Labels = mixedMoment B raw17779step0 raw17779step0Labels := by
      have hz : ∀ j, raw17779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17779step0 = (fun i j => raw17779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17779step0 raw17779; decide +kernel
      have hl : raw17779step0Labels = raw17779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17779 raw17779Labels permutation346 hz
    mixedMoment B raw17779step0 raw17779step0Labels = mixedMoment B raw17779step1 raw17779step1Labels := by
      have ha : raw17779step1 = (fun i j => raw17779step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17779step1 raw17779step0; decide +kernel
      have hl : raw17779step1Labels = raw17779step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17779step0 raw17779step0Labels permutation124 permutation5
    mixedMoment B raw17779step1 raw17779step1Labels = mixedMoment B raw17779step2 raw17779step2Labels := by
      have ha : raw17779step2 = raw17779step1 := by apply Matrix.ext; unfold raw17779step2 raw17779step1; decide +kernel
      have hl : raw17779step1Labels = labelEmbedding8 ∘ raw17779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17779step1 raw17779step1Labels raw17779step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw17780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17780 raw17780Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw17780 raw17780Labels = mixedMoment B raw17780step0 raw17780step0Labels := by
      have hz : ∀ j, raw17780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17780step0 = (fun i j => raw17780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17780step0 raw17780; decide +kernel
      have hl : raw17780step0Labels = raw17780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17780 raw17780Labels permutation346 hz
    mixedMoment B raw17780step0 raw17780step0Labels = mixedMoment B raw17780step1 raw17780step1Labels := by
      have ha : raw17780step1 = (fun i j => raw17780step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17780step1 raw17780step0; decide +kernel
      have hl : raw17780step1Labels = raw17780step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17780step0 raw17780step0Labels permutation127 permutation5
    mixedMoment B raw17780step1 raw17780step1Labels = mixedMoment B raw17780step2 raw17780step2Labels := by
      have ha : raw17780step2 = raw17780step1 := by apply Matrix.ext; unfold raw17780step2 raw17780step1; decide +kernel
      have hl : raw17780step1Labels = labelEmbedding8 ∘ raw17780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17780step1 raw17780step1Labels raw17780step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw17781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17781 raw17781Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw17781 raw17781Labels = mixedMoment B raw17781step0 raw17781step0Labels := by
      have hz : ∀ j, raw17781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17781step0 = (fun i j => raw17781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17781step0 raw17781; decide +kernel
      have hl : raw17781step0Labels = raw17781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17781 raw17781Labels permutation346 hz
    mixedMoment B raw17781step0 raw17781step0Labels = mixedMoment B raw17781step1 raw17781step1Labels := by
      have ha : raw17781step1 = (fun i j => raw17781step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17781step1 raw17781step0; decide +kernel
      have hl : raw17781step1Labels = raw17781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17781step0 raw17781step0Labels permutation150 permutation3
    mixedMoment B raw17781step1 raw17781step1Labels = mixedMoment B raw17781step2 raw17781step2Labels := by
      have ha : raw17781step2 = -raw17781step1 := by apply Matrix.ext; change ∀ i j, raw17781step2 i j = -(raw17781step1 i j); unfold raw17781step2 raw17781step1; decide +kernel
      have hl : raw17781step2Labels = raw17781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17781step2 raw17781step2Labels = mixedMoment B raw17781step3 raw17781step3Labels := by
      have ha : raw17781step3 = raw17781step2 := by apply Matrix.ext; unfold raw17781step3 raw17781step2; decide +kernel
      have hl : raw17781step2Labels = labelEmbedding6 ∘ raw17781step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17781step2 raw17781step2Labels raw17781step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw17782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17782 raw17782Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw17782 raw17782Labels = mixedMoment B raw17782step0 raw17782step0Labels := by
      have ha : raw17782step0 = (fun i j => raw17782 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17782step0 raw17782; decide +kernel
      have hl : raw17782step0Labels = raw17782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17782 raw17782Labels permutation686 permutation3
    mixedMoment B raw17782step0 raw17782step0Labels = mixedMoment B raw17782step1 raw17782step1Labels := by
      have ha : raw17782step1 = -raw17782step0 := by apply Matrix.ext; change ∀ i j, raw17782step1 i j = -(raw17782step0 i j); unfold raw17782step1 raw17782step0; decide +kernel
      have hl : raw17782step1Labels = raw17782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17782step1 raw17782step1Labels = mixedMoment B raw17782step2 raw17782step2Labels := by
      have ha : raw17782step2 = raw17782step1 := by apply Matrix.ext; unfold raw17782step2 raw17782step1; decide +kernel
      have hl : raw17782step1Labels = labelEmbedding6 ∘ raw17782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17782step1 raw17782step1Labels raw17782step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw17783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17783 raw17783Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw17783 raw17783Labels = mixedMoment B raw17783step0 raw17783step0Labels := by
      have hz : ∀ j, raw17783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17783step0 = (fun i j => raw17783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17783step0 raw17783; decide +kernel
      have hl : raw17783step0Labels = raw17783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17783 raw17783Labels permutation346 hz
    mixedMoment B raw17783step0 raw17783step0Labels = mixedMoment B raw17783step1 raw17783step1Labels := by
      have ha : raw17783step1 = (fun i j => raw17783step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17783step1 raw17783step0; decide +kernel
      have hl : raw17783step1Labels = raw17783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17783step0 raw17783step0Labels permutation149 permutation3
    mixedMoment B raw17783step1 raw17783step1Labels = mixedMoment B raw17783step2 raw17783step2Labels := by
      have ha : raw17783step2 = -raw17783step1 := by apply Matrix.ext; change ∀ i j, raw17783step2 i j = -(raw17783step1 i j); unfold raw17783step2 raw17783step1; decide +kernel
      have hl : raw17783step2Labels = raw17783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17783step2 raw17783step2Labels = mixedMoment B raw17783step3 raw17783step3Labels := by
      have ha : raw17783step3 = raw17783step2 := by apply Matrix.ext; unfold raw17783step3 raw17783step2; decide +kernel
      have hl : raw17783step2Labels = labelEmbedding6 ∘ raw17783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17783step2 raw17783step2Labels raw17783step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw17784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17784 raw17784Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17784 raw17784Labels = mixedMoment B raw17784step0 raw17784step0Labels := by
      have hz : ∀ j, raw17784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17784step0 = (fun i j => raw17784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17784step0 raw17784; decide +kernel
      have hl : raw17784step0Labels = raw17784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17784 raw17784Labels permutation346 hz
    mixedMoment B raw17784step0 raw17784step0Labels = mixedMoment B raw17784step1 raw17784step1Labels := by
      have ha : raw17784step1 = (fun i j => raw17784step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17784step1 raw17784step0; decide +kernel
      have hl : raw17784step1Labels = raw17784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17784step0 raw17784step0Labels permutation151 permutation3
    mixedMoment B raw17784step1 raw17784step1Labels = mixedMoment B raw17784step2 raw17784step2Labels := by
      have ha : raw17784step2 = -raw17784step1 := by apply Matrix.ext; change ∀ i j, raw17784step2 i j = -(raw17784step1 i j); unfold raw17784step2 raw17784step1; decide +kernel
      have hl : raw17784step2Labels = raw17784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17784step2 raw17784step2Labels = mixedMoment B raw17784step3 raw17784step3Labels := by
      have ha : raw17784step3 = raw17784step2 := by apply Matrix.ext; unfold raw17784step3 raw17784step2; decide +kernel
      have hl : raw17784step2Labels = labelEmbedding6 ∘ raw17784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17784step2 raw17784step2Labels raw17784step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17785 raw17785Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw17785 raw17785Labels = mixedMoment B raw17785step0 raw17785step0Labels := by
      have hz : ∀ j, raw17785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17785step0 = (fun i j => raw17785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17785step0 raw17785; decide +kernel
      have hl : raw17785step0Labels = raw17785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17785 raw17785Labels permutation346 hz
    mixedMoment B raw17785step0 raw17785step0Labels = mixedMoment B raw17785step1 raw17785step1Labels := by
      have ha : raw17785step1 = (fun i j => raw17785step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17785step1 raw17785step0; decide +kernel
      have hl : raw17785step1Labels = raw17785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17785step0 raw17785step0Labels permutation56 permutation3
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw17786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17786 raw17786Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw17786 raw17786Labels = mixedMoment B raw17786step0 raw17786step0Labels := by
      have ha : raw17786step0 = (fun i j => raw17786 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17786step0 raw17786; decide +kernel
      have hl : raw17786step0Labels = raw17786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17786 raw17786Labels permutation683 permutation3
    mixedMoment B raw17786step0 raw17786step0Labels = mixedMoment B raw17786step1 raw17786step1Labels := by
      have ha : raw17786step1 = -raw17786step0 := by apply Matrix.ext; change ∀ i j, raw17786step1 i j = -(raw17786step0 i j); unfold raw17786step1 raw17786step0; decide +kernel
      have hl : raw17786step1Labels = raw17786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw17787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17787 raw17787Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw17787 raw17787Labels = mixedMoment B raw17787step0 raw17787step0Labels := by
      have hz : ∀ j, raw17787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17787step0 = (fun i j => raw17787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17787step0 raw17787; decide +kernel
      have hl : raw17787step0Labels = raw17787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17787 raw17787Labels permutation346 hz
    mixedMoment B raw17787step0 raw17787step0Labels = mixedMoment B raw17787step1 raw17787step1Labels := by
      have ha : raw17787step1 = (fun i j => raw17787step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17787step1 raw17787step0; decide +kernel
      have hl : raw17787step1Labels = raw17787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17787step0 raw17787step0Labels permutation146 permutation3
    mixedMoment B raw17787step1 raw17787step1Labels = mixedMoment B raw17787step2 raw17787step2Labels := by
      have ha : raw17787step2 = -raw17787step1 := by apply Matrix.ext; change ∀ i j, raw17787step2 i j = -(raw17787step1 i j); unfold raw17787step2 raw17787step1; decide +kernel
      have hl : raw17787step2Labels = raw17787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw17788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17788 raw17788Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw17788 raw17788Labels = mixedMoment B raw17788step0 raw17788step0Labels := by
      have hz : ∀ j, raw17788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17788step0 = (fun i j => raw17788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17788step0 raw17788; decide +kernel
      have hl : raw17788step0Labels = raw17788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17788 raw17788Labels permutation346 hz
    mixedMoment B raw17788step0 raw17788step0Labels = mixedMoment B raw17788step1 raw17788step1Labels := by
      have ha : raw17788step1 = (fun i j => raw17788step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17788step1 raw17788step0; decide +kernel
      have hl : raw17788step1Labels = raw17788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17788step0 raw17788step0Labels permutation150 permutation3
    mixedMoment B raw17788step1 raw17788step1Labels = mixedMoment B raw17788step2 raw17788step2Labels := by
      have ha : raw17788step2 = -raw17788step1 := by apply Matrix.ext; change ∀ i j, raw17788step2 i j = -(raw17788step1 i j); unfold raw17788step2 raw17788step1; decide +kernel
      have hl : raw17788step2Labels = raw17788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw17789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17789 raw17789Labels = mixedMoment B node4050 node4050Labels := by
  calc
    mixedMoment B raw17789 raw17789Labels = mixedMoment B raw17789step0 raw17789step0Labels := by
      have hz : ∀ j, raw17789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17789step0 = (fun i j => raw17789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17789step0 raw17789; decide +kernel
      have hl : raw17789step0Labels = raw17789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17789 raw17789Labels permutation346 hz
    mixedMoment B raw17789step0 raw17789step0Labels = mixedMoment B raw17789step1 raw17789step1Labels := by
      have ha : raw17789step1 = (fun i j => raw17789step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17789step1 raw17789step0; decide +kernel
      have hl : raw17789step1Labels = raw17789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17789step0 raw17789step0Labels permutation126 permutation3
    mixedMoment B raw17789step1 raw17789step1Labels = mixedMoment B raw17789step2 raw17789step2Labels := by
      have ha : raw17789step2 = -raw17789step1 := by apply Matrix.ext; change ∀ i j, raw17789step2 i j = -(raw17789step1 i j); unfold raw17789step2 raw17789step1; decide +kernel
      have hl : raw17789step2Labels = raw17789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4050 node4050Labels := by rfl

def raw17790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17790 raw17790Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw17790 raw17790Labels = mixedMoment B raw17790step0 raw17790step0Labels := by
      have hz : ∀ j, raw17790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17790step0 = (fun i j => raw17790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17790step0 raw17790; decide +kernel
      have hl : raw17790step0Labels = raw17790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17790 raw17790Labels permutation346 hz
    mixedMoment B raw17790step0 raw17790step0Labels = mixedMoment B raw17790step1 raw17790step1Labels := by
      have hz : ∀ j, raw17790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17790step1 = (fun i j => raw17790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17790step1 raw17790step0; decide +kernel
      have hl : raw17790step1Labels = raw17790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17790step0 raw17790step0Labels permutation56 hz
    mixedMoment B raw17790step1 raw17790step1Labels = mixedMoment B raw17790step2 raw17790step2Labels := by
      have ha : raw17790step2 = (fun i j => raw17790step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17790step2 raw17790step1; decide +kernel
      have hl : raw17790step2Labels = raw17790step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17790step1 raw17790step1Labels permutation8 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw17791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17791 raw17791Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw17791 raw17791Labels = mixedMoment B raw17791step0 raw17791step0Labels := by
      have ha : raw17791step0 = (fun i j => raw17791 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17791step0 raw17791; decide +kernel
      have hl : raw17791step0Labels = raw17791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17791 raw17791Labels permutation271 permutation3
    _ = mixedMoment B node3683 node3683Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
