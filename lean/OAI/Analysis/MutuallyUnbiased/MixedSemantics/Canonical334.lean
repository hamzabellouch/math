import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42752Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42752 raw42752Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw42752 raw42752Labels = mixedMoment B raw42752step0 raw42752step0Labels := by
      have hz : ∀ j, raw42752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42752step0 = (fun i j => raw42752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42752step0 raw42752; decide +kernel
      have hl : raw42752step0Labels = raw42752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42752 raw42752Labels permutation434 hz
    mixedMoment B raw42752step0 raw42752step0Labels = mixedMoment B raw42752step1 raw42752step1Labels := by
      have ha : raw42752step1 = raw42752step0 := by apply Matrix.ext; unfold raw42752step1 raw42752step0; decide +kernel
      have hl : raw42752step0Labels = labelEmbedding1 ∘ raw42752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42752step0 raw42752step0Labels raw42752step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw42753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42753Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42753step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw42753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw42753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42753 raw42753Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw42753 raw42753Labels = mixedMoment B raw42753step0 raw42753step0Labels := by
      have hz : ∀ j, raw42753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42753step0 = (fun i j => raw42753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42753step0 raw42753; decide +kernel
      have hl : raw42753step0Labels = raw42753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42753 raw42753Labels permutation434 hz
    mixedMoment B raw42753step0 raw42753step0Labels = mixedMoment B raw42753step1 raw42753step1Labels := by
      have ha : raw42753step1 = (fun i j => raw42753step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42753step1 raw42753step0; decide +kernel
      have hl : raw42753step1Labels = raw42753step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42753step0 raw42753step0Labels permutation145 permutation7
    mixedMoment B raw42753step1 raw42753step1Labels = mixedMoment B raw42753step2 raw42753step2Labels := by
      have ha : raw42753step2 = raw42753step1 := by apply Matrix.ext; unfold raw42753step2 raw42753step1; decide +kernel
      have hl : raw42753step1Labels = labelEmbedding6 ∘ raw42753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42753step1 raw42753step1Labels raw42753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw42754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42754Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42754 raw42754Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw42754 raw42754Labels = mixedMoment B raw42754step0 raw42754step0Labels := by
      have ha : raw42754step0 = (fun i j => raw42754 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42754step0 raw42754; decide +kernel
      have hl : raw42754step0Labels = raw42754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42754 raw42754Labels permutation158 permutation2
    mixedMoment B raw42754step0 raw42754step0Labels = mixedMoment B raw42754step1 raw42754step1Labels := by
      have ha : raw42754step1 = raw42754step0 := by apply Matrix.ext; unfold raw42754step1 raw42754step0; decide +kernel
      have hl : raw42754step0Labels = labelEmbedding1 ∘ raw42754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42754step0 raw42754step0Labels raw42754step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw42755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42755Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw42755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw42755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42755 raw42755Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw42755 raw42755Labels = mixedMoment B raw42755step0 raw42755step0Labels := by
      have ha : raw42755step0 = (fun i j => raw42755 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42755step0 raw42755; decide +kernel
      have hl : raw42755step0Labels = raw42755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42755 raw42755Labels permutation646 permutation7
    mixedMoment B raw42755step0 raw42755step0Labels = mixedMoment B raw42755step1 raw42755step1Labels := by
      have ha : raw42755step1 = raw42755step0 := by apply Matrix.ext; unfold raw42755step1 raw42755step0; decide +kernel
      have hl : raw42755step0Labels = labelEmbedding6 ∘ raw42755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42755step0 raw42755step0Labels raw42755step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw42756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42756Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42756 raw42756Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw42756 raw42756Labels = mixedMoment B raw42756step0 raw42756step0Labels := by
      have ha : raw42756step0 = (fun i j => raw42756 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42756step0 raw42756; decide +kernel
      have hl : raw42756step0Labels = raw42756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42756 raw42756Labels permutation157 permutation2
    mixedMoment B raw42756step0 raw42756step0Labels = mixedMoment B raw42756step1 raw42756step1Labels := by
      have ha : raw42756step1 = raw42756step0 := by apply Matrix.ext; unfold raw42756step1 raw42756step0; decide +kernel
      have hl : raw42756step0Labels = labelEmbedding1 ∘ raw42756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42756step0 raw42756step0Labels raw42756step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw42757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42757Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42757step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42757step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42757step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42757 raw42757Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw42757 raw42757Labels = mixedMoment B raw42757step0 raw42757step0Labels := by
      have ha : raw42757step0 = (fun i j => raw42757 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42757step0 raw42757; decide +kernel
      have hl : raw42757step0Labels = raw42757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42757 raw42757Labels permutation174 permutation7
    mixedMoment B raw42757step0 raw42757step0Labels = mixedMoment B raw42757step1 raw42757step1Labels := by
      have ha : raw42757step1 = -raw42757step0 := by apply Matrix.ext; change ∀ i j, raw42757step1 i j = -(raw42757step0 i j); unfold raw42757step1 raw42757step0; decide +kernel
      have hl : raw42757step1Labels = raw42757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42757step1 raw42757step1Labels = mixedMoment B raw42757step2 raw42757step2Labels := by
      have ha : raw42757step2 = raw42757step1 := by apply Matrix.ext; unfold raw42757step2 raw42757step1; decide +kernel
      have hl : raw42757step1Labels = labelEmbedding6 ∘ raw42757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42757step1 raw42757step1Labels raw42757step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw42758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42758Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42758 raw42758Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw42758 raw42758Labels = mixedMoment B raw42758step0 raw42758step0Labels := by
      have ha : raw42758step0 = (fun i j => raw42758 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42758step0 raw42758; decide +kernel
      have hl : raw42758step0Labels = raw42758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42758 raw42758Labels permutation155 permutation2
    mixedMoment B raw42758step0 raw42758step0Labels = mixedMoment B raw42758step1 raw42758step1Labels := by
      have ha : raw42758step1 = raw42758step0 := by apply Matrix.ext; unfold raw42758step1 raw42758step0; decide +kernel
      have hl : raw42758step0Labels = labelEmbedding1 ∘ raw42758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42758step0 raw42758step0Labels raw42758step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw42759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42759Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42759 raw42759Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw42759 raw42759Labels = mixedMoment B raw42759step0 raw42759step0Labels := by
      have ha : raw42759step0 = (fun i j => raw42759 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42759step0 raw42759; decide +kernel
      have hl : raw42759step0Labels = raw42759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42759 raw42759Labels permutation168 permutation7
    mixedMoment B raw42759step0 raw42759step0Labels = mixedMoment B raw42759step1 raw42759step1Labels := by
      have ha : raw42759step1 = -raw42759step0 := by apply Matrix.ext; change ∀ i j, raw42759step1 i j = -(raw42759step0 i j); unfold raw42759step1 raw42759step0; decide +kernel
      have hl : raw42759step1Labels = raw42759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42759step1 raw42759step1Labels = mixedMoment B raw42759step2 raw42759step2Labels := by
      have ha : raw42759step2 = raw42759step1 := by apply Matrix.ext; unfold raw42759step2 raw42759step1; decide +kernel
      have hl : raw42759step1Labels = labelEmbedding6 ∘ raw42759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42759step1 raw42759step1Labels raw42759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw42760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42760Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42760 raw42760Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw42760 raw42760Labels = mixedMoment B raw42760step0 raw42760step0Labels := by
      have ha : raw42760step0 = raw42760 := by apply Matrix.ext; unfold raw42760step0 raw42760; decide +kernel
      have hl : raw42760Labels = labelEmbedding1 ∘ raw42760step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42760 raw42760Labels raw42760step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw42761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42761Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw42761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42761 raw42761Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw42761 raw42761Labels = mixedMoment B raw42761step0 raw42761step0Labels := by
      have ha : raw42761step0 = (fun i j => raw42761 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42761step0 raw42761; decide +kernel
      have hl : raw42761step0Labels = raw42761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42761 raw42761Labels permutation170 permutation7
    mixedMoment B raw42761step0 raw42761step0Labels = mixedMoment B raw42761step1 raw42761step1Labels := by
      have ha : raw42761step1 = -raw42761step0 := by apply Matrix.ext; change ∀ i j, raw42761step1 i j = -(raw42761step0 i j); unfold raw42761step1 raw42761step0; decide +kernel
      have hl : raw42761step1Labels = raw42761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42761step1 raw42761step1Labels = mixedMoment B raw42761step2 raw42761step2Labels := by
      have ha : raw42761step2 = raw42761step1 := by apply Matrix.ext; unfold raw42761step2 raw42761step1; decide +kernel
      have hl : raw42761step1Labels = labelEmbedding6 ∘ raw42761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42761step1 raw42761step1Labels raw42761step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw42762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42762Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42762 raw42762Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw42762 raw42762Labels = mixedMoment B raw42762step0 raw42762step0Labels := by
      have ha : raw42762step0 = raw42762 := by apply Matrix.ext; unfold raw42762step0 raw42762; decide +kernel
      have hl : raw42762Labels = labelEmbedding1 ∘ raw42762step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42762 raw42762Labels raw42762step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

def raw42763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42763Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw42763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42763 raw42763Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw42763 raw42763Labels = mixedMoment B raw42763step0 raw42763step0Labels := by
      have ha : raw42763step0 = (fun i j => raw42763 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42763step0 raw42763; decide +kernel
      have hl : raw42763step0Labels = raw42763Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42763 raw42763Labels permutation164 permutation7
    mixedMoment B raw42763step0 raw42763step0Labels = mixedMoment B raw42763step1 raw42763step1Labels := by
      have ha : raw42763step1 = -raw42763step0 := by apply Matrix.ext; change ∀ i j, raw42763step1 i j = -(raw42763step0 i j); unfold raw42763step1 raw42763step0; decide +kernel
      have hl : raw42763step1Labels = raw42763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42763step1 raw42763step1Labels = mixedMoment B raw42763step2 raw42763step2Labels := by
      have ha : raw42763step2 = raw42763step1 := by apply Matrix.ext; unfold raw42763step2 raw42763step1; decide +kernel
      have hl : raw42763step1Labels = labelEmbedding6 ∘ raw42763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42763step1 raw42763step1Labels raw42763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5041 node5041Labels := by rfl

def raw42764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42764Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42764step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42764 raw42764Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw42764 raw42764Labels = mixedMoment B raw42764step0 raw42764step0Labels := by
      have hz : ∀ j, raw42764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42764step0 = (fun i j => raw42764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42764step0 raw42764; decide +kernel
      have hl : raw42764step0Labels = raw42764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42764 raw42764Labels permutation434 hz
    mixedMoment B raw42764step0 raw42764step0Labels = mixedMoment B raw42764step1 raw42764step1Labels := by
      have ha : raw42764step1 = raw42764step0 := by apply Matrix.ext; unfold raw42764step1 raw42764step0; decide +kernel
      have hl : raw42764step0Labels = labelEmbedding1 ∘ raw42764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42764step0 raw42764step0Labels raw42764step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw42765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42765Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42765step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw42765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42765 raw42765Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw42765 raw42765Labels = mixedMoment B raw42765step0 raw42765step0Labels := by
      have hz : ∀ j, raw42765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42765step0 = (fun i j => raw42765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42765step0 raw42765; decide +kernel
      have hl : raw42765step0Labels = raw42765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42765 raw42765Labels permutation434 hz
    mixedMoment B raw42765step0 raw42765step0Labels = mixedMoment B raw42765step1 raw42765step1Labels := by
      have ha : raw42765step1 = (fun i j => raw42765step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42765step1 raw42765step0; decide +kernel
      have hl : raw42765step1Labels = raw42765step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42765step0 raw42765step0Labels permutation121 permutation6
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw42766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42766Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42766step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42766step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42766 raw42766Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw42766 raw42766Labels = mixedMoment B raw42766step0 raw42766step0Labels := by
      have hz : ∀ j, raw42766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42766step0 = (fun i j => raw42766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42766step0 raw42766; decide +kernel
      have hl : raw42766step0Labels = raw42766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42766 raw42766Labels permutation434 hz
    mixedMoment B raw42766step0 raw42766step0Labels = mixedMoment B raw42766step1 raw42766step1Labels := by
      have ha : raw42766step1 = (fun i j => raw42766step0 (permutation142 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42766step1 raw42766step0; decide +kernel
      have hl : raw42766step1Labels = raw42766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42766step0 raw42766step0Labels permutation142 permutation4
    mixedMoment B raw42766step1 raw42766step1Labels = mixedMoment B raw42766step2 raw42766step2Labels := by
      have ha : raw42766step2 = -raw42766step1 := by apply Matrix.ext; change ∀ i j, raw42766step2 i j = -(raw42766step1 i j); unfold raw42766step2 raw42766step1; decide +kernel
      have hl : raw42766step2Labels = raw42766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42766step2 raw42766step2Labels = mixedMoment B raw42766step3 raw42766step3Labels := by
      have ha : raw42766step3 = raw42766step2 := by apply Matrix.ext; unfold raw42766step3 raw42766step2; decide +kernel
      have hl : raw42766step2Labels = labelEmbedding1 ∘ raw42766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42766step2 raw42766step2Labels raw42766step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw42767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42767Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42767step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42767 raw42767Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw42767 raw42767Labels = mixedMoment B raw42767step0 raw42767step0Labels := by
      have hz : ∀ j, raw42767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42767step0 = (fun i j => raw42767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42767step0 raw42767; decide +kernel
      have hl : raw42767step0Labels = raw42767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42767 raw42767Labels permutation434 hz
    mixedMoment B raw42767step0 raw42767step0Labels = mixedMoment B raw42767step1 raw42767step1Labels := by
      have ha : raw42767step1 = (fun i j => raw42767step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42767step1 raw42767step0; decide +kernel
      have hl : raw42767step1Labels = raw42767step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42767step0 raw42767step0Labels permutation143 permutation6
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw42768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42768Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42768step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42768 raw42768Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw42768 raw42768Labels = mixedMoment B raw42768step0 raw42768step0Labels := by
      have ha : raw42768step0 = (fun i j => raw42768 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42768step0 raw42768; decide +kernel
      have hl : raw42768step0Labels = raw42768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42768 raw42768Labels permutation634 permutation4
    mixedMoment B raw42768step0 raw42768step0Labels = mixedMoment B raw42768step1 raw42768step1Labels := by
      have ha : raw42768step1 = -raw42768step0 := by apply Matrix.ext; change ∀ i j, raw42768step1 i j = -(raw42768step0 i j); unfold raw42768step1 raw42768step0; decide +kernel
      have hl : raw42768step1Labels = raw42768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42768step1 raw42768step1Labels = mixedMoment B raw42768step2 raw42768step2Labels := by
      have ha : raw42768step2 = raw42768step1 := by apply Matrix.ext; unfold raw42768step2 raw42768step1; decide +kernel
      have hl : raw42768step1Labels = labelEmbedding1 ∘ raw42768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42768step1 raw42768step1Labels raw42768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw42769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42769Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42769 raw42769Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw42769 raw42769Labels = mixedMoment B raw42769step0 raw42769step0Labels := by
      have ha : raw42769step0 = (fun i j => raw42769 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42769step0 raw42769; decide +kernel
      have hl : raw42769step0Labels = raw42769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42769 raw42769Labels permutation644 permutation6
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw42770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42770Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42770 raw42770Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw42770 raw42770Labels = mixedMoment B raw42770step0 raw42770step0Labels := by
      have ha : raw42770step0 = (fun i j => raw42770 (permutation477 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42770step0 raw42770; decide +kernel
      have hl : raw42770step0Labels = raw42770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42770 raw42770Labels permutation477 permutation4
    mixedMoment B raw42770step0 raw42770step0Labels = mixedMoment B raw42770step1 raw42770step1Labels := by
      have ha : raw42770step1 = -raw42770step0 := by apply Matrix.ext; change ∀ i j, raw42770step1 i j = -(raw42770step0 i j); unfold raw42770step1 raw42770step0; decide +kernel
      have hl : raw42770step1Labels = raw42770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42770step1 raw42770step1Labels = mixedMoment B raw42770step2 raw42770step2Labels := by
      have ha : raw42770step2 = raw42770step1 := by apply Matrix.ext; unfold raw42770step2 raw42770step1; decide +kernel
      have hl : raw42770step1Labels = labelEmbedding1 ∘ raw42770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42770step1 raw42770step1Labels raw42770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw42771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42771Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42771 raw42771Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw42771 raw42771Labels = mixedMoment B raw42771step0 raw42771step0Labels := by
      have ha : raw42771step0 = (fun i j => raw42771 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42771step0 raw42771; decide +kernel
      have hl : raw42771step0Labels = raw42771Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42771 raw42771Labels permutation478 permutation6
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw42772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42772Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42772 raw42772Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw42772 raw42772Labels = mixedMoment B raw42772step0 raw42772step0Labels := by
      have ha : raw42772step0 = (fun i j => raw42772 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42772step0 raw42772; decide +kernel
      have hl : raw42772step0Labels = raw42772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42772 raw42772Labels permutation155 permutation2
    mixedMoment B raw42772step0 raw42772step0Labels = mixedMoment B raw42772step1 raw42772step1Labels := by
      have ha : raw42772step1 = raw42772step0 := by apply Matrix.ext; unfold raw42772step1 raw42772step0; decide +kernel
      have hl : raw42772step0Labels = labelEmbedding1 ∘ raw42772step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42772step0 raw42772step0Labels raw42772step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw42773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42773Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw42773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42773 raw42773Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw42773 raw42773Labels = mixedMoment B raw42773step0 raw42773step0Labels := by
      have ha : raw42773step0 = (fun i j => raw42773 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42773step0 raw42773; decide +kernel
      have hl : raw42773step0Labels = raw42773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42773 raw42773Labels permutation480 permutation6
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw42774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42774Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42774 raw42774Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw42774 raw42774Labels = mixedMoment B raw42774step0 raw42774step0Labels := by
      have ha : raw42774step0 = (fun i j => raw42774 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42774step0 raw42774; decide +kernel
      have hl : raw42774step0Labels = raw42774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42774 raw42774Labels permutation156 permutation2
    mixedMoment B raw42774step0 raw42774step0Labels = mixedMoment B raw42774step1 raw42774step1Labels := by
      have ha : raw42774step1 = raw42774step0 := by apply Matrix.ext; unfold raw42774step1 raw42774step0; decide +kernel
      have hl : raw42774step0Labels = labelEmbedding1 ∘ raw42774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42774step0 raw42774step0Labels raw42774step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw42775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42775Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw42775step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42775 raw42775Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw42775 raw42775Labels = mixedMoment B raw42775step0 raw42775step0Labels := by
      have ha : raw42775step0 = (fun i j => raw42775 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42775step0 raw42775; decide +kernel
      have hl : raw42775step0Labels = raw42775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42775 raw42775Labels permutation170 permutation7
    mixedMoment B raw42775step0 raw42775step0Labels = mixedMoment B raw42775step1 raw42775step1Labels := by
      have ha : raw42775step1 = -raw42775step0 := by apply Matrix.ext; change ∀ i j, raw42775step1 i j = -(raw42775step0 i j); unfold raw42775step1 raw42775step0; decide +kernel
      have hl : raw42775step1Labels = raw42775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42775step1 raw42775step1Labels = mixedMoment B raw42775step2 raw42775step2Labels := by
      have ha : raw42775step2 = raw42775step1 := by apply Matrix.ext; unfold raw42775step2 raw42775step1; decide +kernel
      have hl : raw42775step1Labels = labelEmbedding6 ∘ raw42775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42775step1 raw42775step1Labels raw42775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw42776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42776Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42776step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42776step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42776step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42776 raw42776Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw42776 raw42776Labels = mixedMoment B raw42776step0 raw42776step0Labels := by
      have hz : ∀ j, raw42776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42776step0 = (fun i j => raw42776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42776step0 raw42776; decide +kernel
      have hl : raw42776step0Labels = raw42776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42776 raw42776Labels permutation434 hz
    mixedMoment B raw42776step0 raw42776step0Labels = mixedMoment B raw42776step1 raw42776step1Labels := by
      have hz : ∀ j, raw42776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42776step1 = (fun i j => raw42776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42776step1 raw42776step0; decide +kernel
      have hl : raw42776step1Labels = raw42776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42776step0 raw42776step0Labels permutation80 hz
    mixedMoment B raw42776step1 raw42776step1Labels = mixedMoment B raw42776step2 raw42776step2Labels := by
      have ha : raw42776step2 = (fun i j => raw42776step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42776step2 raw42776step1; decide +kernel
      have hl : raw42776step2Labels = raw42776step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42776step1 raw42776step1Labels permutation22 permutation4
    mixedMoment B raw42776step2 raw42776step2Labels = mixedMoment B raw42776step3 raw42776step3Labels := by
      have ha : raw42776step3 = -raw42776step2 := by apply Matrix.ext; change ∀ i j, raw42776step3 i j = -(raw42776step2 i j); unfold raw42776step3 raw42776step2; decide +kernel
      have hl : raw42776step3Labels = raw42776step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42776step3 raw42776step3Labels = mixedMoment B raw42776step4 raw42776step4Labels := by
      have ha : raw42776step4 = raw42776step3 := by apply Matrix.ext; unfold raw42776step4 raw42776step3; decide +kernel
      have hl : raw42776step3Labels = labelEmbedding1 ∘ raw42776step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42776step3 raw42776step3Labels raw42776step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw42777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42777Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42777step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42777step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw42777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42777 raw42777Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw42777 raw42777Labels = mixedMoment B raw42777step0 raw42777step0Labels := by
      have hz : ∀ j, raw42777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42777step0 = (fun i j => raw42777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42777step0 raw42777; decide +kernel
      have hl : raw42777step0Labels = raw42777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42777 raw42777Labels permutation434 hz
    mixedMoment B raw42777step0 raw42777step0Labels = mixedMoment B raw42777step1 raw42777step1Labels := by
      have hz : ∀ j, raw42777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42777step1 = (fun i j => raw42777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42777step1 raw42777step0; decide +kernel
      have hl : raw42777step1Labels = raw42777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42777step0 raw42777step0Labels permutation80 hz
    mixedMoment B raw42777step1 raw42777step1Labels = mixedMoment B raw42777step2 raw42777step2Labels := by
      have ha : raw42777step2 = (fun i j => raw42777step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42777step2 raw42777step1; decide +kernel
      have hl : raw42777step2Labels = raw42777step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42777step1 raw42777step1Labels permutation25 permutation6
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw42778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42778Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42778step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42778step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42778 raw42778Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw42778 raw42778Labels = mixedMoment B raw42778step0 raw42778step0Labels := by
      have hz : ∀ j, raw42778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42778step0 = (fun i j => raw42778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42778step0 raw42778; decide +kernel
      have hl : raw42778step0Labels = raw42778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42778 raw42778Labels permutation434 hz
    mixedMoment B raw42778step0 raw42778step0Labels = mixedMoment B raw42778step1 raw42778step1Labels := by
      have hz : ∀ j, raw42778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42778step1 = (fun i j => raw42778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42778step1 raw42778step0; decide +kernel
      have hl : raw42778step1Labels = raw42778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42778step0 raw42778step0Labels permutation80 hz
    mixedMoment B raw42778step1 raw42778step1Labels = mixedMoment B raw42778step2 raw42778step2Labels := by
      have ha : raw42778step2 = (fun i j => raw42778step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42778step2 raw42778step1; decide +kernel
      have hl : raw42778step2Labels = raw42778step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42778step1 raw42778step1Labels permutation28 permutation4
    mixedMoment B raw42778step2 raw42778step2Labels = mixedMoment B raw42778step3 raw42778step3Labels := by
      have ha : raw42778step3 = -raw42778step2 := by apply Matrix.ext; change ∀ i j, raw42778step3 i j = -(raw42778step2 i j); unfold raw42778step3 raw42778step2; decide +kernel
      have hl : raw42778step3Labels = raw42778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42778step3 raw42778step3Labels = mixedMoment B raw42778step4 raw42778step4Labels := by
      have ha : raw42778step4 = raw42778step3 := by apply Matrix.ext; unfold raw42778step4 raw42778step3; decide +kernel
      have hl : raw42778step3Labels = labelEmbedding1 ∘ raw42778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42778step3 raw42778step3Labels raw42778step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw42779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42779Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42779step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42779step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42779 raw42779Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw42779 raw42779Labels = mixedMoment B raw42779step0 raw42779step0Labels := by
      have hz : ∀ j, raw42779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42779step0 = (fun i j => raw42779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42779step0 raw42779; decide +kernel
      have hl : raw42779step0Labels = raw42779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42779 raw42779Labels permutation434 hz
    mixedMoment B raw42779step0 raw42779step0Labels = mixedMoment B raw42779step1 raw42779step1Labels := by
      have hz : ∀ j, raw42779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42779step1 = (fun i j => raw42779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42779step1 raw42779step0; decide +kernel
      have hl : raw42779step1Labels = raw42779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42779step0 raw42779step0Labels permutation80 hz
    mixedMoment B raw42779step1 raw42779step1Labels = mixedMoment B raw42779step2 raw42779step2Labels := by
      have ha : raw42779step2 = (fun i j => raw42779step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42779step2 raw42779step1; decide +kernel
      have hl : raw42779step2Labels = raw42779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42779step1 raw42779step1Labels permutation29 permutation6
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw42780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42780Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42780step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42780step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42780step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42780step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42780 raw42780Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw42780 raw42780Labels = mixedMoment B raw42780step0 raw42780step0Labels := by
      have hz : ∀ j, raw42780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42780step0 = (fun i j => raw42780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42780step0 raw42780; decide +kernel
      have hl : raw42780step0Labels = raw42780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42780 raw42780Labels permutation346 hz
    mixedMoment B raw42780step0 raw42780step0Labels = mixedMoment B raw42780step1 raw42780step1Labels := by
      have ha : raw42780step1 = (fun i j => raw42780step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42780step1 raw42780step0; decide +kernel
      have hl : raw42780step1Labels = raw42780step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42780step0 raw42780step0Labels permutation139 permutation4
    mixedMoment B raw42780step1 raw42780step1Labels = mixedMoment B raw42780step2 raw42780step2Labels := by
      have ha : raw42780step2 = -raw42780step1 := by apply Matrix.ext; change ∀ i j, raw42780step2 i j = -(raw42780step1 i j); unfold raw42780step2 raw42780step1; decide +kernel
      have hl : raw42780step2Labels = raw42780step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42780step2 raw42780step2Labels = mixedMoment B raw42780step3 raw42780step3Labels := by
      have ha : raw42780step3 = raw42780step2 := by apply Matrix.ext; unfold raw42780step3 raw42780step2; decide +kernel
      have hl : raw42780step2Labels = labelEmbedding1 ∘ raw42780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42780step2 raw42780step2Labels raw42780step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw42781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42781Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42781step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42781 raw42781Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw42781 raw42781Labels = mixedMoment B raw42781step0 raw42781step0Labels := by
      have hz : ∀ j, raw42781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42781step0 = (fun i j => raw42781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42781step0 raw42781; decide +kernel
      have hl : raw42781step0Labels = raw42781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42781 raw42781Labels permutation346 hz
    mixedMoment B raw42781step0 raw42781step0Labels = mixedMoment B raw42781step1 raw42781step1Labels := by
      have ha : raw42781step1 = (fun i j => raw42781step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42781step1 raw42781step0; decide +kernel
      have hl : raw42781step1Labels = raw42781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42781step0 raw42781step0Labels permutation149 permutation6
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw42782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42782Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42782step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42782step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42782 raw42782Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw42782 raw42782Labels = mixedMoment B raw42782step0 raw42782step0Labels := by
      have hz : ∀ j, raw42782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42782step0 = (fun i j => raw42782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42782step0 raw42782; decide +kernel
      have hl : raw42782step0Labels = raw42782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42782 raw42782Labels permutation346 hz
    mixedMoment B raw42782step0 raw42782step0Labels = mixedMoment B raw42782step1 raw42782step1Labels := by
      have ha : raw42782step1 = (fun i j => raw42782step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42782step1 raw42782step0; decide +kernel
      have hl : raw42782step1Labels = raw42782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42782step0 raw42782step0Labels permutation94 permutation4
    mixedMoment B raw42782step1 raw42782step1Labels = mixedMoment B raw42782step2 raw42782step2Labels := by
      have ha : raw42782step2 = -raw42782step1 := by apply Matrix.ext; change ∀ i j, raw42782step2 i j = -(raw42782step1 i j); unfold raw42782step2 raw42782step1; decide +kernel
      have hl : raw42782step2Labels = raw42782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42782step2 raw42782step2Labels = mixedMoment B raw42782step3 raw42782step3Labels := by
      have ha : raw42782step3 = raw42782step2 := by apply Matrix.ext; unfold raw42782step3 raw42782step2; decide +kernel
      have hl : raw42782step2Labels = labelEmbedding1 ∘ raw42782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42782step2 raw42782step2Labels raw42782step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw42783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42783Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42783step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42783 raw42783Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw42783 raw42783Labels = mixedMoment B raw42783step0 raw42783step0Labels := by
      have hz : ∀ j, raw42783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42783step0 = (fun i j => raw42783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42783step0 raw42783; decide +kernel
      have hl : raw42783step0Labels = raw42783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42783 raw42783Labels permutation346 hz
    mixedMoment B raw42783step0 raw42783step0Labels = mixedMoment B raw42783step1 raw42783step1Labels := by
      have ha : raw42783step1 = (fun i j => raw42783step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42783step1 raw42783step0; decide +kernel
      have hl : raw42783step1Labels = raw42783step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42783step0 raw42783step0Labels permutation95 permutation6
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw42784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42784Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42784step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42784step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42784 raw42784Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw42784 raw42784Labels = mixedMoment B raw42784step0 raw42784step0Labels := by
      have hz : ∀ j, raw42784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42784step0 = (fun i j => raw42784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42784step0 raw42784; decide +kernel
      have hl : raw42784step0Labels = raw42784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42784 raw42784Labels permutation346 hz
    mixedMoment B raw42784step0 raw42784step0Labels = mixedMoment B raw42784step1 raw42784step1Labels := by
      have ha : raw42784step1 = (fun i j => raw42784step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42784step1 raw42784step0; decide +kernel
      have hl : raw42784step1Labels = raw42784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42784step0 raw42784step0Labels permutation89 permutation4
    mixedMoment B raw42784step1 raw42784step1Labels = mixedMoment B raw42784step2 raw42784step2Labels := by
      have ha : raw42784step2 = -raw42784step1 := by apply Matrix.ext; change ∀ i j, raw42784step2 i j = -(raw42784step1 i j); unfold raw42784step2 raw42784step1; decide +kernel
      have hl : raw42784step2Labels = raw42784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42784step2 raw42784step2Labels = mixedMoment B raw42784step3 raw42784step3Labels := by
      have ha : raw42784step3 = raw42784step2 := by apply Matrix.ext; unfold raw42784step3 raw42784step2; decide +kernel
      have hl : raw42784step2Labels = labelEmbedding1 ∘ raw42784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42784step2 raw42784step2Labels raw42784step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw42785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42785Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42785step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw42785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42785 raw42785Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw42785 raw42785Labels = mixedMoment B raw42785step0 raw42785step0Labels := by
      have hz : ∀ j, raw42785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42785step0 = (fun i j => raw42785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42785step0 raw42785; decide +kernel
      have hl : raw42785step0Labels = raw42785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42785 raw42785Labels permutation346 hz
    mixedMoment B raw42785step0 raw42785step0Labels = mixedMoment B raw42785step1 raw42785step1Labels := by
      have ha : raw42785step1 = (fun i j => raw42785step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42785step1 raw42785step0; decide +kernel
      have hl : raw42785step1Labels = raw42785step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42785step0 raw42785step0Labels permutation97 permutation6
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw42786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42786Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42786step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42786step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42786step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42786step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42786 raw42786Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw42786 raw42786Labels = mixedMoment B raw42786step0 raw42786step0Labels := by
      have hz : ∀ j, raw42786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42786step0 = (fun i j => raw42786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42786step0 raw42786; decide +kernel
      have hl : raw42786step0Labels = raw42786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42786 raw42786Labels permutation346 hz
    mixedMoment B raw42786step0 raw42786step0Labels = mixedMoment B raw42786step1 raw42786step1Labels := by
      have ha : raw42786step1 = (fun i j => raw42786step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42786step1 raw42786step0; decide +kernel
      have hl : raw42786step1Labels = raw42786step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42786step0 raw42786step0Labels permutation94 permutation4
    mixedMoment B raw42786step1 raw42786step1Labels = mixedMoment B raw42786step2 raw42786step2Labels := by
      have ha : raw42786step2 = -raw42786step1 := by apply Matrix.ext; change ∀ i j, raw42786step2 i j = -(raw42786step1 i j); unfold raw42786step2 raw42786step1; decide +kernel
      have hl : raw42786step2Labels = raw42786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42786step2 raw42786step2Labels = mixedMoment B raw42786step3 raw42786step3Labels := by
      have ha : raw42786step3 = raw42786step2 := by apply Matrix.ext; unfold raw42786step3 raw42786step2; decide +kernel
      have hl : raw42786step2Labels = labelEmbedding1 ∘ raw42786step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42786step2 raw42786step2Labels raw42786step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw42787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42787Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42787step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42787 raw42787Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw42787 raw42787Labels = mixedMoment B raw42787step0 raw42787step0Labels := by
      have hz : ∀ j, raw42787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42787step0 = (fun i j => raw42787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42787step0 raw42787; decide +kernel
      have hl : raw42787step0Labels = raw42787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42787 raw42787Labels permutation346 hz
    mixedMoment B raw42787step0 raw42787step0Labels = mixedMoment B raw42787step1 raw42787step1Labels := by
      have ha : raw42787step1 = (fun i j => raw42787step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42787step1 raw42787step0; decide +kernel
      have hl : raw42787step1Labels = raw42787step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42787step0 raw42787step0Labels permutation95 permutation6
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw42788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42788Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42788 raw42788Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw42788 raw42788Labels = mixedMoment B raw42788step0 raw42788step0Labels := by
      have ha : raw42788step0 = (fun i j => raw42788 (permutation494 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42788step0 raw42788; decide +kernel
      have hl : raw42788step0Labels = raw42788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42788 raw42788Labels permutation494 permutation4
    mixedMoment B raw42788step0 raw42788step0Labels = mixedMoment B raw42788step1 raw42788step1Labels := by
      have ha : raw42788step1 = -raw42788step0 := by apply Matrix.ext; change ∀ i j, raw42788step1 i j = -(raw42788step0 i j); unfold raw42788step1 raw42788step0; decide +kernel
      have hl : raw42788step1Labels = raw42788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42788step1 raw42788step1Labels = mixedMoment B raw42788step2 raw42788step2Labels := by
      have ha : raw42788step2 = raw42788step1 := by apply Matrix.ext; unfold raw42788step2 raw42788step1; decide +kernel
      have hl : raw42788step1Labels = labelEmbedding1 ∘ raw42788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42788step1 raw42788step1Labels raw42788step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw42789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42789Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42789 raw42789Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw42789 raw42789Labels = mixedMoment B raw42789step0 raw42789step0Labels := by
      have ha : raw42789step0 = (fun i j => raw42789 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42789step0 raw42789; decide +kernel
      have hl : raw42789step0Labels = raw42789Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42789 raw42789Labels permutation502 permutation6
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw42790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42790Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42790 raw42790Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw42790 raw42790Labels = mixedMoment B raw42790step0 raw42790step0Labels := by
      have ha : raw42790step0 = (fun i j => raw42790 (permutation494 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42790step0 raw42790; decide +kernel
      have hl : raw42790step0Labels = raw42790Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42790 raw42790Labels permutation494 permutation4
    mixedMoment B raw42790step0 raw42790step0Labels = mixedMoment B raw42790step1 raw42790step1Labels := by
      have ha : raw42790step1 = -raw42790step0 := by apply Matrix.ext; change ∀ i j, raw42790step1 i j = -(raw42790step0 i j); unfold raw42790step1 raw42790step0; decide +kernel
      have hl : raw42790step1Labels = raw42790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42790step1 raw42790step1Labels = mixedMoment B raw42790step2 raw42790step2Labels := by
      have ha : raw42790step2 = raw42790step1 := by apply Matrix.ext; unfold raw42790step2 raw42790step1; decide +kernel
      have hl : raw42790step1Labels = labelEmbedding1 ∘ raw42790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42790step1 raw42790step1Labels raw42790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw42791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42791Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42791 raw42791Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw42791 raw42791Labels = mixedMoment B raw42791step0 raw42791step0Labels := by
      have ha : raw42791step0 = (fun i j => raw42791 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42791step0 raw42791; decide +kernel
      have hl : raw42791step0Labels = raw42791Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42791 raw42791Labels permutation502 permutation6
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw42792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42792Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42792step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42792step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42792 raw42792Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw42792 raw42792Labels = mixedMoment B raw42792step0 raw42792step0Labels := by
      have hz : ∀ j, raw42792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42792step0 = (fun i j => raw42792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42792step0 raw42792; decide +kernel
      have hl : raw42792step0Labels = raw42792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42792 raw42792Labels permutation434 hz
    mixedMoment B raw42792step0 raw42792step0Labels = mixedMoment B raw42792step1 raw42792step1Labels := by
      have ha : raw42792step1 = (fun i j => raw42792step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42792step1 raw42792step0; decide +kernel
      have hl : raw42792step1Labels = raw42792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42792step0 raw42792step0Labels permutation103 permutation4
    mixedMoment B raw42792step1 raw42792step1Labels = mixedMoment B raw42792step2 raw42792step2Labels := by
      have ha : raw42792step2 = -raw42792step1 := by apply Matrix.ext; change ∀ i j, raw42792step2 i j = -(raw42792step1 i j); unfold raw42792step2 raw42792step1; decide +kernel
      have hl : raw42792step2Labels = raw42792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42792step2 raw42792step2Labels = mixedMoment B raw42792step3 raw42792step3Labels := by
      have ha : raw42792step3 = raw42792step2 := by apply Matrix.ext; unfold raw42792step3 raw42792step2; decide +kernel
      have hl : raw42792step2Labels = labelEmbedding1 ∘ raw42792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42792step2 raw42792step2Labels raw42792step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw42793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42793Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42793step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42793 raw42793Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw42793 raw42793Labels = mixedMoment B raw42793step0 raw42793step0Labels := by
      have hz : ∀ j, raw42793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42793step0 = (fun i j => raw42793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42793step0 raw42793; decide +kernel
      have hl : raw42793step0Labels = raw42793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42793 raw42793Labels permutation434 hz
    mixedMoment B raw42793step0 raw42793step0Labels = mixedMoment B raw42793step1 raw42793step1Labels := by
      have ha : raw42793step1 = (fun i j => raw42793step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42793step1 raw42793step0; decide +kernel
      have hl : raw42793step1Labels = raw42793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42793step0 raw42793step0Labels permutation103 permutation6
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw42794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42794Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42794 raw42794Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw42794 raw42794Labels = mixedMoment B raw42794step0 raw42794step0Labels := by
      have ha : raw42794step0 = (fun i j => raw42794 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42794step0 raw42794; decide +kernel
      have hl : raw42794step0Labels = raw42794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42794 raw42794Labels permutation394 permutation4
    mixedMoment B raw42794step0 raw42794step0Labels = mixedMoment B raw42794step1 raw42794step1Labels := by
      have ha : raw42794step1 = -raw42794step0 := by apply Matrix.ext; change ∀ i j, raw42794step1 i j = -(raw42794step0 i j); unfold raw42794step1 raw42794step0; decide +kernel
      have hl : raw42794step1Labels = raw42794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42794step1 raw42794step1Labels = mixedMoment B raw42794step2 raw42794step2Labels := by
      have ha : raw42794step2 = raw42794step1 := by apply Matrix.ext; unfold raw42794step2 raw42794step1; decide +kernel
      have hl : raw42794step1Labels = labelEmbedding1 ∘ raw42794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42794step1 raw42794step1Labels raw42794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw42795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42795Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42795 raw42795Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw42795 raw42795Labels = mixedMoment B raw42795step0 raw42795step0Labels := by
      have ha : raw42795step0 = (fun i j => raw42795 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42795step0 raw42795; decide +kernel
      have hl : raw42795step0Labels = raw42795Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42795 raw42795Labels permutation394 permutation6
    _ = mixedMoment B node4757 node4757Labels := by rfl

def raw42796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42796Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42796 raw42796Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw42796 raw42796Labels = mixedMoment B raw42796step0 raw42796step0Labels := by
      have ha : raw42796step0 = (fun i j => raw42796 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42796step0 raw42796; decide +kernel
      have hl : raw42796step0Labels = raw42796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42796 raw42796Labels permutation158 permutation2
    mixedMoment B raw42796step0 raw42796step0Labels = mixedMoment B raw42796step1 raw42796step1Labels := by
      have ha : raw42796step1 = raw42796step0 := by apply Matrix.ext; unfold raw42796step1 raw42796step0; decide +kernel
      have hl : raw42796step0Labels = labelEmbedding1 ∘ raw42796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42796step0 raw42796step0Labels raw42796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw42797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42797Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42797step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42797 raw42797Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw42797 raw42797Labels = mixedMoment B raw42797step0 raw42797step0Labels := by
      have ha : raw42797step0 = (fun i j => raw42797 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42797step0 raw42797; decide +kernel
      have hl : raw42797step0Labels = raw42797Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42797 raw42797Labels permutation166 permutation7
    mixedMoment B raw42797step0 raw42797step0Labels = mixedMoment B raw42797step1 raw42797step1Labels := by
      have ha : raw42797step1 = -raw42797step0 := by apply Matrix.ext; change ∀ i j, raw42797step1 i j = -(raw42797step0 i j); unfold raw42797step1 raw42797step0; decide +kernel
      have hl : raw42797step1Labels = raw42797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42797step1 raw42797step1Labels = mixedMoment B raw42797step2 raw42797step2Labels := by
      have ha : raw42797step2 = raw42797step1 := by apply Matrix.ext; unfold raw42797step2 raw42797step1; decide +kernel
      have hl : raw42797step1Labels = labelEmbedding6 ∘ raw42797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42797step1 raw42797step1Labels raw42797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw42798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42798Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42798 raw42798Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw42798 raw42798Labels = mixedMoment B raw42798step0 raw42798step0Labels := by
      have hz : ∀ j, raw42798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42798step0 = (fun i j => raw42798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42798step0 raw42798; decide +kernel
      have hl : raw42798step0Labels = raw42798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42798 raw42798Labels permutation434 hz
    mixedMoment B raw42798step0 raw42798step0Labels = mixedMoment B raw42798step1 raw42798step1Labels := by
      have ha : raw42798step1 = raw42798step0 := by apply Matrix.ext; unfold raw42798step1 raw42798step0; decide +kernel
      have hl : raw42798step0Labels = labelEmbedding1 ∘ raw42798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42798step0 raw42798step0Labels raw42798step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw42799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42799Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42799step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw42799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42799step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42799step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42799 raw42799Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw42799 raw42799Labels = mixedMoment B raw42799step0 raw42799step0Labels := by
      have hz : ∀ j, raw42799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42799step0 = (fun i j => raw42799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42799step0 raw42799; decide +kernel
      have hl : raw42799step0Labels = raw42799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42799 raw42799Labels permutation434 hz
    mixedMoment B raw42799step0 raw42799step0Labels = mixedMoment B raw42799step1 raw42799step1Labels := by
      have ha : raw42799step1 = (fun i j => raw42799step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42799step1 raw42799step0; decide +kernel
      have hl : raw42799step1Labels = raw42799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42799step0 raw42799step0Labels permutation34 permutation7
    mixedMoment B raw42799step1 raw42799step1Labels = mixedMoment B raw42799step2 raw42799step2Labels := by
      have ha : raw42799step2 = -raw42799step1 := by apply Matrix.ext; change ∀ i j, raw42799step2 i j = -(raw42799step1 i j); unfold raw42799step2 raw42799step1; decide +kernel
      have hl : raw42799step2Labels = raw42799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42799step2 raw42799step2Labels = mixedMoment B raw42799step3 raw42799step3Labels := by
      have ha : raw42799step3 = raw42799step2 := by apply Matrix.ext; unfold raw42799step3 raw42799step2; decide +kernel
      have hl : raw42799step2Labels = labelEmbedding6 ∘ raw42799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42799step2 raw42799step2Labels raw42799step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw42800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42800Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42800 raw42800Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw42800 raw42800Labels = mixedMoment B raw42800step0 raw42800step0Labels := by
      have ha : raw42800step0 = (fun i j => raw42800 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42800step0 raw42800; decide +kernel
      have hl : raw42800step0Labels = raw42800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42800 raw42800Labels permutation157 permutation2
    mixedMoment B raw42800step0 raw42800step0Labels = mixedMoment B raw42800step1 raw42800step1Labels := by
      have ha : raw42800step1 = raw42800step0 := by apply Matrix.ext; unfold raw42800step1 raw42800step0; decide +kernel
      have hl : raw42800step0Labels = labelEmbedding1 ∘ raw42800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42800step0 raw42800step0Labels raw42800step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw42801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42801Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42801step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42801 raw42801Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw42801 raw42801Labels = mixedMoment B raw42801step0 raw42801step0Labels := by
      have ha : raw42801step0 = (fun i j => raw42801 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42801step0 raw42801; decide +kernel
      have hl : raw42801step0Labels = raw42801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42801 raw42801Labels permutation174 permutation7
    mixedMoment B raw42801step0 raw42801step0Labels = mixedMoment B raw42801step1 raw42801step1Labels := by
      have ha : raw42801step1 = -raw42801step0 := by apply Matrix.ext; change ∀ i j, raw42801step1 i j = -(raw42801step0 i j); unfold raw42801step1 raw42801step0; decide +kernel
      have hl : raw42801step1Labels = raw42801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42801step1 raw42801step1Labels = mixedMoment B raw42801step2 raw42801step2Labels := by
      have ha : raw42801step2 = raw42801step1 := by apply Matrix.ext; unfold raw42801step2 raw42801step1; decide +kernel
      have hl : raw42801step1Labels = labelEmbedding6 ∘ raw42801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42801step1 raw42801step1Labels raw42801step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw42802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42802Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42802step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42802 raw42802Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw42802 raw42802Labels = mixedMoment B raw42802step0 raw42802step0Labels := by
      have hz : ∀ j, raw42802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42802step0 = (fun i j => raw42802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42802step0 raw42802; decide +kernel
      have hl : raw42802step0Labels = raw42802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42802 raw42802Labels permutation434 hz
    mixedMoment B raw42802step0 raw42802step0Labels = mixedMoment B raw42802step1 raw42802step1Labels := by
      have ha : raw42802step1 = (fun i j => raw42802step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42802step1 raw42802step0; decide +kernel
      have hl : raw42802step1Labels = raw42802step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42802step0 raw42802step0Labels permutation145 permutation4
    mixedMoment B raw42802step1 raw42802step1Labels = mixedMoment B raw42802step2 raw42802step2Labels := by
      have ha : raw42802step2 = -raw42802step1 := by apply Matrix.ext; change ∀ i j, raw42802step2 i j = -(raw42802step1 i j); unfold raw42802step2 raw42802step1; decide +kernel
      have hl : raw42802step2Labels = raw42802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42802step2 raw42802step2Labels = mixedMoment B raw42802step3 raw42802step3Labels := by
      have ha : raw42802step3 = raw42802step2 := by apply Matrix.ext; unfold raw42802step3 raw42802step2; decide +kernel
      have hl : raw42802step2Labels = labelEmbedding1 ∘ raw42802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42802step2 raw42802step2Labels raw42802step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw42803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42803Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42803step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42803 raw42803Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw42803 raw42803Labels = mixedMoment B raw42803step0 raw42803step0Labels := by
      have hz : ∀ j, raw42803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42803step0 = (fun i j => raw42803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42803step0 raw42803; decide +kernel
      have hl : raw42803step0Labels = raw42803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42803 raw42803Labels permutation434 hz
    mixedMoment B raw42803step0 raw42803step0Labels = mixedMoment B raw42803step1 raw42803step1Labels := by
      have ha : raw42803step1 = (fun i j => raw42803step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42803step1 raw42803step0; decide +kernel
      have hl : raw42803step1Labels = raw42803step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42803step0 raw42803step0Labels permutation145 permutation6
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw42804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42804Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42804step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42804 raw42804Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw42804 raw42804Labels = mixedMoment B raw42804step0 raw42804step0Labels := by
      have ha : raw42804step0 = (fun i j => raw42804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42804step0 raw42804; decide +kernel
      have hl : raw42804step0Labels = raw42804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42804 raw42804Labels permutation157 permutation2
    mixedMoment B raw42804step0 raw42804step0Labels = mixedMoment B raw42804step1 raw42804step1Labels := by
      have ha : raw42804step1 = raw42804step0 := by apply Matrix.ext; unfold raw42804step1 raw42804step0; decide +kernel
      have hl : raw42804step0Labels = labelEmbedding1 ∘ raw42804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42804step0 raw42804step0Labels raw42804step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw42805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42805Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw42805step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42805step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42805 raw42805Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw42805 raw42805Labels = mixedMoment B raw42805step0 raw42805step0Labels := by
      have ha : raw42805step0 = (fun i j => raw42805 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42805step0 raw42805; decide +kernel
      have hl : raw42805step0Labels = raw42805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42805 raw42805Labels permutation171 permutation7
    mixedMoment B raw42805step0 raw42805step0Labels = mixedMoment B raw42805step1 raw42805step1Labels := by
      have ha : raw42805step1 = -raw42805step0 := by apply Matrix.ext; change ∀ i j, raw42805step1 i j = -(raw42805step0 i j); unfold raw42805step1 raw42805step0; decide +kernel
      have hl : raw42805step1Labels = raw42805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42805step1 raw42805step1Labels = mixedMoment B raw42805step2 raw42805step2Labels := by
      have ha : raw42805step2 = raw42805step1 := by apply Matrix.ext; unfold raw42805step2 raw42805step1; decide +kernel
      have hl : raw42805step1Labels = labelEmbedding6 ∘ raw42805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42805step1 raw42805step1Labels raw42805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw42806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42806Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42806step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42806step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42806step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42806 raw42806Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw42806 raw42806Labels = mixedMoment B raw42806step0 raw42806step0Labels := by
      have hz : ∀ j, raw42806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42806step0 = (fun i j => raw42806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42806step0 raw42806; decide +kernel
      have hl : raw42806step0Labels = raw42806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42806 raw42806Labels permutation434 hz
    mixedMoment B raw42806step0 raw42806step0Labels = mixedMoment B raw42806step1 raw42806step1Labels := by
      have hz : ∀ j, raw42806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42806step1 = (fun i j => raw42806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42806step1 raw42806step0; decide +kernel
      have hl : raw42806step1Labels = raw42806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42806step0 raw42806step0Labels permutation80 hz
    mixedMoment B raw42806step1 raw42806step1Labels = mixedMoment B raw42806step2 raw42806step2Labels := by
      have ha : raw42806step2 = (fun i j => raw42806step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42806step2 raw42806step1; decide +kernel
      have hl : raw42806step2Labels = raw42806step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42806step1 raw42806step1Labels permutation31 permutation4
    mixedMoment B raw42806step2 raw42806step2Labels = mixedMoment B raw42806step3 raw42806step3Labels := by
      have ha : raw42806step3 = -raw42806step2 := by apply Matrix.ext; change ∀ i j, raw42806step3 i j = -(raw42806step2 i j); unfold raw42806step3 raw42806step2; decide +kernel
      have hl : raw42806step3Labels = raw42806step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42806step3 raw42806step3Labels = mixedMoment B raw42806step4 raw42806step4Labels := by
      have ha : raw42806step4 = raw42806step3 := by apply Matrix.ext; unfold raw42806step4 raw42806step3; decide +kernel
      have hl : raw42806step3Labels = labelEmbedding1 ∘ raw42806step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42806step3 raw42806step3Labels raw42806step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw42807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42807Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42807step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42807step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42807 raw42807Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw42807 raw42807Labels = mixedMoment B raw42807step0 raw42807step0Labels := by
      have hz : ∀ j, raw42807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42807step0 = (fun i j => raw42807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42807step0 raw42807; decide +kernel
      have hl : raw42807step0Labels = raw42807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42807 raw42807Labels permutation434 hz
    mixedMoment B raw42807step0 raw42807step0Labels = mixedMoment B raw42807step1 raw42807step1Labels := by
      have hz : ∀ j, raw42807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42807step1 = (fun i j => raw42807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42807step1 raw42807step0; decide +kernel
      have hl : raw42807step1Labels = raw42807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42807step0 raw42807step0Labels permutation80 hz
    mixedMoment B raw42807step1 raw42807step1Labels = mixedMoment B raw42807step2 raw42807step2Labels := by
      have ha : raw42807step2 = (fun i j => raw42807step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42807step2 raw42807step1; decide +kernel
      have hl : raw42807step2Labels = raw42807step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42807step1 raw42807step1Labels permutation31 permutation6
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw42808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42808Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw42808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42808step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42808step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42808 raw42808Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw42808 raw42808Labels = mixedMoment B raw42808step0 raw42808step0Labels := by
      have hz : ∀ j, raw42808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42808step0 = (fun i j => raw42808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42808step0 raw42808; decide +kernel
      have hl : raw42808step0Labels = raw42808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42808 raw42808Labels permutation346 hz
    mixedMoment B raw42808step0 raw42808step0Labels = mixedMoment B raw42808step1 raw42808step1Labels := by
      have ha : raw42808step1 = (fun i j => raw42808step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42808step1 raw42808step0; decide +kernel
      have hl : raw42808step1Labels = raw42808step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42808step0 raw42808step0Labels permutation97 permutation4
    mixedMoment B raw42808step1 raw42808step1Labels = mixedMoment B raw42808step2 raw42808step2Labels := by
      have ha : raw42808step2 = -raw42808step1 := by apply Matrix.ext; change ∀ i j, raw42808step2 i j = -(raw42808step1 i j); unfold raw42808step2 raw42808step1; decide +kernel
      have hl : raw42808step2Labels = raw42808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42808step2 raw42808step2Labels = mixedMoment B raw42808step3 raw42808step3Labels := by
      have ha : raw42808step3 = raw42808step2 := by apply Matrix.ext; unfold raw42808step3 raw42808step2; decide +kernel
      have hl : raw42808step2Labels = labelEmbedding1 ∘ raw42808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42808step2 raw42808step2Labels raw42808step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw42809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42809Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42809step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42809 raw42809Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw42809 raw42809Labels = mixedMoment B raw42809step0 raw42809step0Labels := by
      have hz : ∀ j, raw42809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42809step0 = (fun i j => raw42809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42809step0 raw42809; decide +kernel
      have hl : raw42809step0Labels = raw42809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42809 raw42809Labels permutation346 hz
    mixedMoment B raw42809step0 raw42809step0Labels = mixedMoment B raw42809step1 raw42809step1Labels := by
      have ha : raw42809step1 = (fun i j => raw42809step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42809step1 raw42809step0; decide +kernel
      have hl : raw42809step1Labels = raw42809step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42809step0 raw42809step0Labels permutation97 permutation6
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw42810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42810Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42810step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42810 raw42810Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw42810 raw42810Labels = mixedMoment B raw42810step0 raw42810step0Labels := by
      have hz : ∀ j, raw42810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42810step0 = (fun i j => raw42810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42810step0 raw42810; decide +kernel
      have hl : raw42810step0Labels = raw42810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42810 raw42810Labels permutation346 hz
    mixedMoment B raw42810step0 raw42810step0Labels = mixedMoment B raw42810step1 raw42810step1Labels := by
      have ha : raw42810step1 = (fun i j => raw42810step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42810step1 raw42810step0; decide +kernel
      have hl : raw42810step1Labels = raw42810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42810step0 raw42810step0Labels permutation37 permutation2
    mixedMoment B raw42810step1 raw42810step1Labels = mixedMoment B raw42810step2 raw42810step2Labels := by
      have ha : raw42810step2 = raw42810step1 := by apply Matrix.ext; unfold raw42810step2 raw42810step1; decide +kernel
      have hl : raw42810step1Labels = labelEmbedding1 ∘ raw42810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42810step1 raw42810step1Labels raw42810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw42811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42811Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42811step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42811 raw42811Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw42811 raw42811Labels = mixedMoment B raw42811step0 raw42811step0Labels := by
      have hz : ∀ j, raw42811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42811step0 = (fun i j => raw42811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42811step0 raw42811; decide +kernel
      have hl : raw42811step0Labels = raw42811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42811 raw42811Labels permutation346 hz
    mixedMoment B raw42811step0 raw42811step0Labels = mixedMoment B raw42811step1 raw42811step1Labels := by
      have ha : raw42811step1 = (fun i j => raw42811step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42811step1 raw42811step0; decide +kernel
      have hl : raw42811step1Labels = raw42811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42811step0 raw42811step0Labels permutation97 permutation6
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw42812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42812Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-2, -2, 4]]
def raw42812step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42812step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42812step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42812step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42812 raw42812Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw42812 raw42812Labels = mixedMoment B raw42812step0 raw42812step0Labels := by
      have hz : ∀ j, raw42812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42812step0 = (fun i j => raw42812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42812step0 raw42812; decide +kernel
      have hl : raw42812step0Labels = raw42812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42812 raw42812Labels permutation434 hz
    mixedMoment B raw42812step0 raw42812step0Labels = mixedMoment B raw42812step1 raw42812step1Labels := by
      have hz : ∀ j, raw42812step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42812step1 = (fun i j => raw42812step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42812step1 raw42812step0; decide +kernel
      have hl : raw42812step1Labels = raw42812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42812step0 raw42812step0Labels permutation80 hz
    mixedMoment B raw42812step1 raw42812step1Labels = mixedMoment B raw42812step2 raw42812step2Labels := by
      have ha : raw42812step2 = (fun i j => raw42812step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42812step2 raw42812step1; decide +kernel
      have hl : raw42812step2Labels = raw42812step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42812step1 raw42812step1Labels permutation19 permutation4
    mixedMoment B raw42812step2 raw42812step2Labels = mixedMoment B raw42812step3 raw42812step3Labels := by
      have ha : raw42812step3 = -raw42812step2 := by apply Matrix.ext; change ∀ i j, raw42812step3 i j = -(raw42812step2 i j); unfold raw42812step3 raw42812step2; decide +kernel
      have hl : raw42812step3Labels = raw42812step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42812step3 raw42812step3Labels = mixedMoment B raw42812step4 raw42812step4Labels := by
      have ha : raw42812step4 = raw42812step3 := by apply Matrix.ext; unfold raw42812step4 raw42812step3; decide +kernel
      have hl : raw42812step3Labels = labelEmbedding1 ∘ raw42812step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42812step3 raw42812step3Labels raw42812step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw42813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42813Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42813step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42813step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw42813step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42813 raw42813Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw42813 raw42813Labels = mixedMoment B raw42813step0 raw42813step0Labels := by
      have hz : ∀ j, raw42813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42813step0 = (fun i j => raw42813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42813step0 raw42813; decide +kernel
      have hl : raw42813step0Labels = raw42813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42813 raw42813Labels permutation434 hz
    mixedMoment B raw42813step0 raw42813step0Labels = mixedMoment B raw42813step1 raw42813step1Labels := by
      have hz : ∀ j, raw42813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42813step1 = (fun i j => raw42813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42813step1 raw42813step0; decide +kernel
      have hl : raw42813step1Labels = raw42813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42813step0 raw42813step0Labels permutation80 hz
    mixedMoment B raw42813step1 raw42813step1Labels = mixedMoment B raw42813step2 raw42813step2Labels := by
      have ha : raw42813step2 = (fun i j => raw42813step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42813step2 raw42813step1; decide +kernel
      have hl : raw42813step2Labels = raw42813step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42813step1 raw42813step1Labels permutation11 permutation6
    mixedMoment B raw42813step2 raw42813step2Labels = mixedMoment B raw42813step3 raw42813step3Labels := by
      have ha : raw42813step3 = -raw42813step2 := by apply Matrix.ext; change ∀ i j, raw42813step3 i j = -(raw42813step2 i j); unfold raw42813step3 raw42813step2; decide +kernel
      have hl : raw42813step3Labels = raw42813step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw42814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42814Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42814 raw42814Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw42814 raw42814Labels = mixedMoment B raw42814step0 raw42814step0Labels := by
      have hz : ∀ j, raw42814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42814step0 = (fun i j => raw42814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42814step0 raw42814; decide +kernel
      have hl : raw42814step0Labels = raw42814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42814 raw42814Labels permutation346 hz
    mixedMoment B raw42814step0 raw42814step0Labels = mixedMoment B raw42814step1 raw42814step1Labels := by
      have ha : raw42814step1 = (fun i j => raw42814step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42814step1 raw42814step0; decide +kernel
      have hl : raw42814step1Labels = raw42814step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42814step0 raw42814step0Labels permutation65 permutation4
    mixedMoment B raw42814step1 raw42814step1Labels = mixedMoment B raw42814step2 raw42814step2Labels := by
      have ha : raw42814step2 = -raw42814step1 := by apply Matrix.ext; change ∀ i j, raw42814step2 i j = -(raw42814step1 i j); unfold raw42814step2 raw42814step1; decide +kernel
      have hl : raw42814step2Labels = raw42814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42814step2 raw42814step2Labels = mixedMoment B raw42814step3 raw42814step3Labels := by
      have ha : raw42814step3 = raw42814step2 := by apply Matrix.ext; unfold raw42814step3 raw42814step2; decide +kernel
      have hl : raw42814step2Labels = labelEmbedding1 ∘ raw42814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42814step2 raw42814step2Labels raw42814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw42815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42815Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42815step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw42815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42815 raw42815Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw42815 raw42815Labels = mixedMoment B raw42815step0 raw42815step0Labels := by
      have hz : ∀ j, raw42815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42815step0 = (fun i j => raw42815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42815step0 raw42815; decide +kernel
      have hl : raw42815step0Labels = raw42815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42815 raw42815Labels permutation346 hz
    mixedMoment B raw42815step0 raw42815step0Labels = mixedMoment B raw42815step1 raw42815step1Labels := by
      have ha : raw42815step1 = (fun i j => raw42815step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42815step1 raw42815step0; decide +kernel
      have hl : raw42815step1Labels = raw42815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42815step0 raw42815step0Labels permutation53 permutation6
    mixedMoment B raw42815step1 raw42815step1Labels = mixedMoment B raw42815step2 raw42815step2Labels := by
      have ha : raw42815step2 = -raw42815step1 := by apply Matrix.ext; change ∀ i j, raw42815step2 i j = -(raw42815step1 i j); unfold raw42815step2 raw42815step1; decide +kernel
      have hl : raw42815step2Labels = raw42815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw42816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42816Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42816 raw42816Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42816 raw42816Labels = mixedMoment B raw42816step0 raw42816step0Labels := by
      have hz : ∀ j, raw42816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42816step0 = (fun i j => raw42816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42816step0 raw42816; decide +kernel
      have hl : raw42816step0Labels = raw42816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42816 raw42816Labels permutation434 hz
    mixedMoment B raw42816step0 raw42816step0Labels = mixedMoment B raw42816step1 raw42816step1Labels := by
      have ha : raw42816step1 = (fun i j => raw42816step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42816step1 raw42816step0; decide +kernel
      have hl : raw42816step1Labels = raw42816step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42816step0 raw42816step0Labels permutation49 permutation4
    mixedMoment B raw42816step1 raw42816step1Labels = mixedMoment B raw42816step2 raw42816step2Labels := by
      have ha : raw42816step2 = raw42816step1 := by apply Matrix.ext; unfold raw42816step2 raw42816step1; decide +kernel
      have hl : raw42816step1Labels = labelEmbedding1 ∘ raw42816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42816step1 raw42816step1Labels raw42816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw42817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42817Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42817 raw42817Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42817 raw42817Labels = mixedMoment B raw42817step0 raw42817step0Labels := by
      have hz : ∀ j, raw42817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42817step0 = (fun i j => raw42817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42817step0 raw42817; decide +kernel
      have hl : raw42817step0Labels = raw42817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42817 raw42817Labels permutation434 hz
    mixedMoment B raw42817step0 raw42817step0Labels = mixedMoment B raw42817step1 raw42817step1Labels := by
      have ha : raw42817step1 = (fun i j => raw42817step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42817step1 raw42817step0; decide +kernel
      have hl : raw42817step1Labels = raw42817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42817step0 raw42817step0Labels permutation46 permutation6
    mixedMoment B raw42817step1 raw42817step1Labels = mixedMoment B raw42817step2 raw42817step2Labels := by
      have ha : raw42817step2 = -raw42817step1 := by apply Matrix.ext; change ∀ i j, raw42817step2 i j = -(raw42817step1 i j); unfold raw42817step2 raw42817step1; decide +kernel
      have hl : raw42817step2Labels = raw42817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw42818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42818Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42818 raw42818Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw42818 raw42818Labels = mixedMoment B raw42818step0 raw42818step0Labels := by
      have ha : raw42818step0 = (fun i j => raw42818 (permutation259 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42818step0 raw42818; decide +kernel
      have hl : raw42818step0Labels = raw42818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42818 raw42818Labels permutation259 permutation4
    mixedMoment B raw42818step0 raw42818step0Labels = mixedMoment B raw42818step1 raw42818step1Labels := by
      have ha : raw42818step1 = raw42818step0 := by apply Matrix.ext; unfold raw42818step1 raw42818step0; decide +kernel
      have hl : raw42818step0Labels = labelEmbedding1 ∘ raw42818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42818step0 raw42818step0Labels raw42818step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw42819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42819Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42819 raw42819Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw42819 raw42819Labels = mixedMoment B raw42819step0 raw42819step0Labels := by
      have ha : raw42819step0 = (fun i j => raw42819 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42819step0 raw42819; decide +kernel
      have hl : raw42819step0Labels = raw42819Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42819 raw42819Labels permutation259 permutation6
    mixedMoment B raw42819step0 raw42819step0Labels = mixedMoment B raw42819step1 raw42819step1Labels := by
      have ha : raw42819step1 = -raw42819step0 := by apply Matrix.ext; change ∀ i j, raw42819step1 i j = -(raw42819step0 i j); unfold raw42819step1 raw42819step0; decide +kernel
      have hl : raw42819step1Labels = raw42819step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw42820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42820Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42820step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42820 raw42820Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42820 raw42820Labels = mixedMoment B raw42820step0 raw42820step0Labels := by
      have hz : ∀ j, raw42820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42820step0 = (fun i j => raw42820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42820step0 raw42820; decide +kernel
      have hl : raw42820step0Labels = raw42820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42820 raw42820Labels permutation434 hz
    mixedMoment B raw42820step0 raw42820step0Labels = mixedMoment B raw42820step1 raw42820step1Labels := by
      have hz : ∀ j, raw42820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42820step1 = (fun i j => raw42820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42820step1 raw42820step0; decide +kernel
      have hl : raw42820step1Labels = raw42820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42820step0 raw42820step0Labels permutation80 hz
    mixedMoment B raw42820step1 raw42820step1Labels = mixedMoment B raw42820step2 raw42820step2Labels := by
      have ha : raw42820step2 = (fun i j => raw42820step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42820step2 raw42820step1; decide +kernel
      have hl : raw42820step2Labels = raw42820step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42820step1 raw42820step1Labels permutation11 permutation4
    mixedMoment B raw42820step2 raw42820step2Labels = mixedMoment B raw42820step3 raw42820step3Labels := by
      have ha : raw42820step3 = raw42820step2 := by apply Matrix.ext; unfold raw42820step3 raw42820step2; decide +kernel
      have hl : raw42820step2Labels = labelEmbedding1 ∘ raw42820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42820step2 raw42820step2Labels raw42820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw42821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42821Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42821step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42821step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw42821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42821 raw42821Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42821 raw42821Labels = mixedMoment B raw42821step0 raw42821step0Labels := by
      have hz : ∀ j, raw42821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42821step0 = (fun i j => raw42821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42821step0 raw42821; decide +kernel
      have hl : raw42821step0Labels = raw42821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42821 raw42821Labels permutation434 hz
    mixedMoment B raw42821step0 raw42821step0Labels = mixedMoment B raw42821step1 raw42821step1Labels := by
      have hz : ∀ j, raw42821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42821step1 = (fun i j => raw42821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42821step1 raw42821step0; decide +kernel
      have hl : raw42821step1Labels = raw42821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42821step0 raw42821step0Labels permutation80 hz
    mixedMoment B raw42821step1 raw42821step1Labels = mixedMoment B raw42821step2 raw42821step2Labels := by
      have ha : raw42821step2 = (fun i j => raw42821step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42821step2 raw42821step1; decide +kernel
      have hl : raw42821step2Labels = raw42821step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42821step1 raw42821step1Labels permutation10 permutation6
    mixedMoment B raw42821step2 raw42821step2Labels = mixedMoment B raw42821step3 raw42821step3Labels := by
      have ha : raw42821step3 = -raw42821step2 := by apply Matrix.ext; change ∀ i j, raw42821step3 i j = -(raw42821step2 i j); unfold raw42821step3 raw42821step2; decide +kernel
      have hl : raw42821step3Labels = raw42821step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw42822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42822Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42822 raw42822Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw42822 raw42822Labels = mixedMoment B raw42822step0 raw42822step0Labels := by
      have hz : ∀ j, raw42822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42822step0 = (fun i j => raw42822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42822step0 raw42822; decide +kernel
      have hl : raw42822step0Labels = raw42822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42822 raw42822Labels permutation346 hz
    mixedMoment B raw42822step0 raw42822step0Labels = mixedMoment B raw42822step1 raw42822step1Labels := by
      have ha : raw42822step1 = (fun i j => raw42822step0 (permutation55 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42822step1 raw42822step0; decide +kernel
      have hl : raw42822step1Labels = raw42822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42822step0 raw42822step0Labels permutation55 permutation4
    mixedMoment B raw42822step1 raw42822step1Labels = mixedMoment B raw42822step2 raw42822step2Labels := by
      have ha : raw42822step2 = raw42822step1 := by apply Matrix.ext; unfold raw42822step2 raw42822step1; decide +kernel
      have hl : raw42822step1Labels = labelEmbedding1 ∘ raw42822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42822step1 raw42822step1Labels raw42822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw42823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42823Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42823step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw42823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42823 raw42823Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw42823 raw42823Labels = mixedMoment B raw42823step0 raw42823step0Labels := by
      have hz : ∀ j, raw42823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42823step0 = (fun i j => raw42823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42823step0 raw42823; decide +kernel
      have hl : raw42823step0Labels = raw42823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42823 raw42823Labels permutation346 hz
    mixedMoment B raw42823step0 raw42823step0Labels = mixedMoment B raw42823step1 raw42823step1Labels := by
      have ha : raw42823step1 = (fun i j => raw42823step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42823step1 raw42823step0; decide +kernel
      have hl : raw42823step1Labels = raw42823step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42823step0 raw42823step0Labels permutation54 permutation6
    mixedMoment B raw42823step1 raw42823step1Labels = mixedMoment B raw42823step2 raw42823step2Labels := by
      have ha : raw42823step2 = -raw42823step1 := by apply Matrix.ext; change ∀ i j, raw42823step2 i j = -(raw42823step1 i j); unfold raw42823step2 raw42823step1; decide +kernel
      have hl : raw42823step2Labels = raw42823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw42824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42824Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42824 raw42824Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw42824 raw42824Labels = mixedMoment B raw42824step0 raw42824step0Labels := by
      have hz : ∀ j, raw42824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42824step0 = (fun i j => raw42824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42824step0 raw42824; decide +kernel
      have hl : raw42824step0Labels = raw42824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42824 raw42824Labels permutation434 hz
    mixedMoment B raw42824step0 raw42824step0Labels = mixedMoment B raw42824step1 raw42824step1Labels := by
      have ha : raw42824step1 = raw42824step0 := by apply Matrix.ext; unfold raw42824step1 raw42824step0; decide +kernel
      have hl : raw42824step0Labels = labelEmbedding1 ∘ raw42824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42824step0 raw42824step0Labels raw42824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw42825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42825Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42825step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42825 raw42825Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw42825 raw42825Labels = mixedMoment B raw42825step0 raw42825step0Labels := by
      have hz : ∀ j, raw42825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42825step0 = (fun i j => raw42825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42825step0 raw42825; decide +kernel
      have hl : raw42825step0Labels = raw42825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42825 raw42825Labels permutation434 hz
    mixedMoment B raw42825step0 raw42825step0Labels = mixedMoment B raw42825step1 raw42825step1Labels := by
      have ha : raw42825step1 = (fun i j => raw42825step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42825step1 raw42825step0; decide +kernel
      have hl : raw42825step1Labels = raw42825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42825step0 raw42825step0Labels permutation45 permutation6
    mixedMoment B raw42825step1 raw42825step1Labels = mixedMoment B raw42825step2 raw42825step2Labels := by
      have ha : raw42825step2 = -raw42825step1 := by apply Matrix.ext; change ∀ i j, raw42825step2 i j = -(raw42825step1 i j); unfold raw42825step2 raw42825step1; decide +kernel
      have hl : raw42825step2Labels = raw42825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw42826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42826Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42826 raw42826Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42826 raw42826Labels = mixedMoment B raw42826step0 raw42826step0Labels := by
      have ha : raw42826step0 = (fun i j => raw42826 (permutation258 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42826step0 raw42826; decide +kernel
      have hl : raw42826step0Labels = raw42826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42826 raw42826Labels permutation258 permutation4
    mixedMoment B raw42826step0 raw42826step0Labels = mixedMoment B raw42826step1 raw42826step1Labels := by
      have ha : raw42826step1 = raw42826step0 := by apply Matrix.ext; unfold raw42826step1 raw42826step0; decide +kernel
      have hl : raw42826step0Labels = labelEmbedding1 ∘ raw42826step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42826step0 raw42826step0Labels raw42826step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw42827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42827Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42827 raw42827Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42827 raw42827Labels = mixedMoment B raw42827step0 raw42827step0Labels := by
      have ha : raw42827step0 = (fun i j => raw42827 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42827step0 raw42827; decide +kernel
      have hl : raw42827step0Labels = raw42827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42827 raw42827Labels permutation249 permutation6
    mixedMoment B raw42827step0 raw42827step0Labels = mixedMoment B raw42827step1 raw42827step1Labels := by
      have ha : raw42827step1 = -raw42827step0 := by apply Matrix.ext; change ∀ i j, raw42827step1 i j = -(raw42827step0 i j); unfold raw42827step1 raw42827step0; decide +kernel
      have hl : raw42827step1Labels = raw42827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw42828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42828Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42828 raw42828Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42828 raw42828Labels = mixedMoment B raw42828step0 raw42828step0Labels := by
      have ha : raw42828step0 = raw42828 := by apply Matrix.ext; unfold raw42828step0 raw42828; decide +kernel
      have hl : raw42828Labels = labelEmbedding1 ∘ raw42828step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42828 raw42828Labels raw42828step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw42829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42829Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42829step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42829step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42829step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42829 raw42829Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42829 raw42829Labels = mixedMoment B raw42829step0 raw42829step0Labels := by
      have ha : raw42829step0 = (fun i j => raw42829 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42829step0 raw42829; decide +kernel
      have hl : raw42829step0Labels = raw42829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42829 raw42829Labels permutation164 permutation7
    mixedMoment B raw42829step0 raw42829step0Labels = mixedMoment B raw42829step1 raw42829step1Labels := by
      have ha : raw42829step1 = -raw42829step0 := by apply Matrix.ext; change ∀ i j, raw42829step1 i j = -(raw42829step0 i j); unfold raw42829step1 raw42829step0; decide +kernel
      have hl : raw42829step1Labels = raw42829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42829step1 raw42829step1Labels = mixedMoment B raw42829step2 raw42829step2Labels := by
      have ha : raw42829step2 = raw42829step1 := by apply Matrix.ext; unfold raw42829step2 raw42829step1; decide +kernel
      have hl : raw42829step1Labels = labelEmbedding6 ∘ raw42829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42829step1 raw42829step1Labels raw42829step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw42830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42830Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42830 raw42830Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42830 raw42830Labels = mixedMoment B raw42830step0 raw42830step0Labels := by
      have hz : ∀ j, raw42830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42830step0 = (fun i j => raw42830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42830step0 raw42830; decide +kernel
      have hl : raw42830step0Labels = raw42830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42830 raw42830Labels permutation434 hz
    mixedMoment B raw42830step0 raw42830step0Labels = mixedMoment B raw42830step1 raw42830step1Labels := by
      have ha : raw42830step1 = raw42830step0 := by apply Matrix.ext; unfold raw42830step1 raw42830step0; decide +kernel
      have hl : raw42830step0Labels = labelEmbedding1 ∘ raw42830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42830step0 raw42830step0Labels raw42830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw42831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42831Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42831step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw42831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42831step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42831step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42831 raw42831Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42831 raw42831Labels = mixedMoment B raw42831step0 raw42831step0Labels := by
      have hz : ∀ j, raw42831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42831step0 = (fun i j => raw42831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42831step0 raw42831; decide +kernel
      have hl : raw42831step0Labels = raw42831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42831 raw42831Labels permutation434 hz
    mixedMoment B raw42831step0 raw42831step0Labels = mixedMoment B raw42831step1 raw42831step1Labels := by
      have ha : raw42831step1 = (fun i j => raw42831step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42831step1 raw42831step0; decide +kernel
      have hl : raw42831step1Labels = raw42831step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42831step0 raw42831step0Labels permutation34 permutation7
    mixedMoment B raw42831step1 raw42831step1Labels = mixedMoment B raw42831step2 raw42831step2Labels := by
      have ha : raw42831step2 = -raw42831step1 := by apply Matrix.ext; change ∀ i j, raw42831step2 i j = -(raw42831step1 i j); unfold raw42831step2 raw42831step1; decide +kernel
      have hl : raw42831step2Labels = raw42831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42831step2 raw42831step2Labels = mixedMoment B raw42831step3 raw42831step3Labels := by
      have ha : raw42831step3 = raw42831step2 := by apply Matrix.ext; unfold raw42831step3 raw42831step2; decide +kernel
      have hl : raw42831step2Labels = labelEmbedding6 ∘ raw42831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42831step2 raw42831step2Labels raw42831step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw42832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42832Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42832 raw42832Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw42832 raw42832Labels = mixedMoment B raw42832step0 raw42832step0Labels := by
      have ha : raw42832step0 = (fun i j => raw42832 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42832step0 raw42832; decide +kernel
      have hl : raw42832step0Labels = raw42832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42832 raw42832Labels permutation157 permutation2
    mixedMoment B raw42832step0 raw42832step0Labels = mixedMoment B raw42832step1 raw42832step1Labels := by
      have ha : raw42832step1 = raw42832step0 := by apply Matrix.ext; unfold raw42832step1 raw42832step0; decide +kernel
      have hl : raw42832step0Labels = labelEmbedding1 ∘ raw42832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42832step0 raw42832step0Labels raw42832step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw42833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42833Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42833 raw42833Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw42833 raw42833Labels = mixedMoment B raw42833step0 raw42833step0Labels := by
      have ha : raw42833step0 = (fun i j => raw42833 (permutation250 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42833step0 raw42833; decide +kernel
      have hl : raw42833step0Labels = raw42833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42833 raw42833Labels permutation250 permutation6
    mixedMoment B raw42833step0 raw42833step0Labels = mixedMoment B raw42833step1 raw42833step1Labels := by
      have ha : raw42833step1 = -raw42833step0 := by apply Matrix.ext; change ∀ i j, raw42833step1 i j = -(raw42833step0 i j); unfold raw42833step1 raw42833step0; decide +kernel
      have hl : raw42833step1Labels = raw42833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw42834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42834 raw42834Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw42834 raw42834Labels = mixedMoment B raw42834step0 raw42834step0Labels := by
      have hz : ∀ j, raw42834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42834step0 = (fun i j => raw42834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42834step0 raw42834; decide +kernel
      have hl : raw42834step0Labels = raw42834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42834 raw42834Labels permutation434 hz
    mixedMoment B raw42834step0 raw42834step0Labels = mixedMoment B raw42834step1 raw42834step1Labels := by
      have hz : ∀ j, raw42834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42834step1 = (fun i j => raw42834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42834step1 raw42834step0; decide +kernel
      have hl : raw42834step1Labels = raw42834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42834step0 raw42834step0Labels permutation80 hz
    mixedMoment B raw42834step1 raw42834step1Labels = mixedMoment B raw42834step2 raw42834step2Labels := by
      have ha : raw42834step2 = raw42834step1 := by apply Matrix.ext; unfold raw42834step2 raw42834step1; decide +kernel
      have hl : raw42834step1Labels = labelEmbedding1 ∘ raw42834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42834step1 raw42834step1Labels raw42834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw42835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42835step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw42835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42835 raw42835Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw42835 raw42835Labels = mixedMoment B raw42835step0 raw42835step0Labels := by
      have hz : ∀ j, raw42835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42835step0 = (fun i j => raw42835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42835step0 raw42835; decide +kernel
      have hl : raw42835step0Labels = raw42835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42835 raw42835Labels permutation434 hz
    mixedMoment B raw42835step0 raw42835step0Labels = mixedMoment B raw42835step1 raw42835step1Labels := by
      have hz : ∀ j, raw42835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42835step1 = (fun i j => raw42835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42835step1 raw42835step0; decide +kernel
      have hl : raw42835step1Labels = raw42835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42835step0 raw42835step0Labels permutation80 hz
    mixedMoment B raw42835step1 raw42835step1Labels = mixedMoment B raw42835step2 raw42835step2Labels := by
      have ha : raw42835step2 = (fun i j => raw42835step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42835step2 raw42835step1; decide +kernel
      have hl : raw42835step2Labels = raw42835step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42835step1 raw42835step1Labels permutation29 permutation6
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw42836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42836Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42836 raw42836Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42836 raw42836Labels = mixedMoment B raw42836step0 raw42836step0Labels := by
      have hz : ∀ j, raw42836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42836step0 = (fun i j => raw42836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42836step0 raw42836; decide +kernel
      have hl : raw42836step0Labels = raw42836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42836 raw42836Labels permutation346 hz
    mixedMoment B raw42836step0 raw42836step0Labels = mixedMoment B raw42836step1 raw42836step1Labels := by
      have ha : raw42836step1 = (fun i j => raw42836step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42836step1 raw42836step0; decide +kernel
      have hl : raw42836step1Labels = raw42836step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42836step0 raw42836step0Labels permutation54 permutation4
    mixedMoment B raw42836step1 raw42836step1Labels = mixedMoment B raw42836step2 raw42836step2Labels := by
      have ha : raw42836step2 = raw42836step1 := by apply Matrix.ext; unfold raw42836step2 raw42836step1; decide +kernel
      have hl : raw42836step1Labels = labelEmbedding1 ∘ raw42836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42836step1 raw42836step1Labels raw42836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw42837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42837Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42837step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw42837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42837step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42837 raw42837Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42837 raw42837Labels = mixedMoment B raw42837step0 raw42837step0Labels := by
      have hz : ∀ j, raw42837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42837step0 = (fun i j => raw42837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42837step0 raw42837; decide +kernel
      have hl : raw42837step0Labels = raw42837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42837 raw42837Labels permutation346 hz
    mixedMoment B raw42837step0 raw42837step0Labels = mixedMoment B raw42837step1 raw42837step1Labels := by
      have ha : raw42837step1 = (fun i j => raw42837step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42837step1 raw42837step0; decide +kernel
      have hl : raw42837step1Labels = raw42837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42837step0 raw42837step0Labels permutation51 permutation6
    mixedMoment B raw42837step1 raw42837step1Labels = mixedMoment B raw42837step2 raw42837step2Labels := by
      have ha : raw42837step2 = -raw42837step1 := by apply Matrix.ext; change ∀ i j, raw42837step2 i j = -(raw42837step1 i j); unfold raw42837step2 raw42837step1; decide +kernel
      have hl : raw42837step2Labels = raw42837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw42838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42838Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42838 raw42838Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw42838 raw42838Labels = mixedMoment B raw42838step0 raw42838step0Labels := by
      have hz : ∀ j, raw42838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42838step0 = (fun i j => raw42838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42838step0 raw42838; decide +kernel
      have hl : raw42838step0Labels = raw42838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42838 raw42838Labels permutation346 hz
    mixedMoment B raw42838step0 raw42838step0Labels = mixedMoment B raw42838step1 raw42838step1Labels := by
      have ha : raw42838step1 = (fun i j => raw42838step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42838step1 raw42838step0; decide +kernel
      have hl : raw42838step1Labels = raw42838step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42838step0 raw42838step0Labels permutation36 permutation2
    mixedMoment B raw42838step1 raw42838step1Labels = mixedMoment B raw42838step2 raw42838step2Labels := by
      have ha : raw42838step2 = raw42838step1 := by apply Matrix.ext; unfold raw42838step2 raw42838step1; decide +kernel
      have hl : raw42838step1Labels = labelEmbedding1 ∘ raw42838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42838step1 raw42838step1Labels raw42838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw42839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42839Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42839step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42839 raw42839Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw42839 raw42839Labels = mixedMoment B raw42839step0 raw42839step0Labels := by
      have hz : ∀ j, raw42839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42839step0 = (fun i j => raw42839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42839step0 raw42839; decide +kernel
      have hl : raw42839step0Labels = raw42839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42839 raw42839Labels permutation346 hz
    mixedMoment B raw42839step0 raw42839step0Labels = mixedMoment B raw42839step1 raw42839step1Labels := by
      have ha : raw42839step1 = (fun i j => raw42839step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42839step1 raw42839step0; decide +kernel
      have hl : raw42839step1Labels = raw42839step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42839step0 raw42839step0Labels permutation50 permutation6
    mixedMoment B raw42839step1 raw42839step1Labels = mixedMoment B raw42839step2 raw42839step2Labels := by
      have ha : raw42839step2 = -raw42839step1 := by apply Matrix.ext; change ∀ i j, raw42839step2 i j = -(raw42839step1 i j); unfold raw42839step2 raw42839step1; decide +kernel
      have hl : raw42839step2Labels = raw42839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw42840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42840Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42840step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42840 raw42840Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw42840 raw42840Labels = mixedMoment B raw42840step0 raw42840step0Labels := by
      have hz : ∀ j, raw42840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42840step0 = (fun i j => raw42840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42840step0 raw42840; decide +kernel
      have hl : raw42840step0Labels = raw42840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42840 raw42840Labels permutation434 hz
    mixedMoment B raw42840step0 raw42840step0Labels = mixedMoment B raw42840step1 raw42840step1Labels := by
      have ha : raw42840step1 = (fun i j => raw42840step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42840step1 raw42840step0; decide +kernel
      have hl : raw42840step1Labels = raw42840step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42840step0 raw42840step0Labels permutation101 permutation4
    mixedMoment B raw42840step1 raw42840step1Labels = mixedMoment B raw42840step2 raw42840step2Labels := by
      have ha : raw42840step2 = -raw42840step1 := by apply Matrix.ext; change ∀ i j, raw42840step2 i j = -(raw42840step1 i j); unfold raw42840step2 raw42840step1; decide +kernel
      have hl : raw42840step2Labels = raw42840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42840step2 raw42840step2Labels = mixedMoment B raw42840step3 raw42840step3Labels := by
      have ha : raw42840step3 = raw42840step2 := by apply Matrix.ext; unfold raw42840step3 raw42840step2; decide +kernel
      have hl : raw42840step2Labels = labelEmbedding1 ∘ raw42840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42840step2 raw42840step2Labels raw42840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw42841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42841Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42841step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw42841step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw42841step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42841step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw42841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42841 raw42841Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw42841 raw42841Labels = mixedMoment B raw42841step0 raw42841step0Labels := by
      have hz : ∀ j, raw42841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42841step0 = (fun i j => raw42841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42841step0 raw42841; decide +kernel
      have hl : raw42841step0Labels = raw42841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42841 raw42841Labels permutation434 hz
    mixedMoment B raw42841step0 raw42841step0Labels = mixedMoment B raw42841step1 raw42841step1Labels := by
      have ha : raw42841step1 = (fun i j => raw42841step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42841step1 raw42841step0; decide +kernel
      have hl : raw42841step1Labels = raw42841step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42841step0 raw42841step0Labels permutation35 permutation7
    mixedMoment B raw42841step1 raw42841step1Labels = mixedMoment B raw42841step2 raw42841step2Labels := by
      have ha : raw42841step2 = -raw42841step1 := by apply Matrix.ext; change ∀ i j, raw42841step2 i j = -(raw42841step1 i j); unfold raw42841step2 raw42841step1; decide +kernel
      have hl : raw42841step2Labels = raw42841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42841step2 raw42841step2Labels = mixedMoment B raw42841step3 raw42841step3Labels := by
      have ha : raw42841step3 = raw42841step2 := by apply Matrix.ext; unfold raw42841step3 raw42841step2; decide +kernel
      have hl : raw42841step2Labels = labelEmbedding6 ∘ raw42841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42841step2 raw42841step2Labels raw42841step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

def raw42842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42842Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42842 raw42842Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw42842 raw42842Labels = mixedMoment B raw42842step0 raw42842step0Labels := by
      have ha : raw42842step0 = (fun i j => raw42842 (permutation392 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42842step0 raw42842; decide +kernel
      have hl : raw42842step0Labels = raw42842Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42842 raw42842Labels permutation392 permutation4
    mixedMoment B raw42842step0 raw42842step0Labels = mixedMoment B raw42842step1 raw42842step1Labels := by
      have ha : raw42842step1 = -raw42842step0 := by apply Matrix.ext; change ∀ i j, raw42842step1 i j = -(raw42842step0 i j); unfold raw42842step1 raw42842step0; decide +kernel
      have hl : raw42842step1Labels = raw42842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42842step1 raw42842step1Labels = mixedMoment B raw42842step2 raw42842step2Labels := by
      have ha : raw42842step2 = raw42842step1 := by apply Matrix.ext; unfold raw42842step2 raw42842step1; decide +kernel
      have hl : raw42842step1Labels = labelEmbedding1 ∘ raw42842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42842step1 raw42842step1Labels raw42842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

def raw42843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42843Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw42843step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw42843step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42843step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw42843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42843 raw42843Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw42843 raw42843Labels = mixedMoment B raw42843step0 raw42843step0Labels := by
      have ha : raw42843step0 = (fun i j => raw42843 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42843step0 raw42843; decide +kernel
      have hl : raw42843step0Labels = raw42843Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42843 raw42843Labels permutation173 permutation7
    mixedMoment B raw42843step0 raw42843step0Labels = mixedMoment B raw42843step1 raw42843step1Labels := by
      have ha : raw42843step1 = -raw42843step0 := by apply Matrix.ext; change ∀ i j, raw42843step1 i j = -(raw42843step0 i j); unfold raw42843step1 raw42843step0; decide +kernel
      have hl : raw42843step1Labels = raw42843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42843step1 raw42843step1Labels = mixedMoment B raw42843step2 raw42843step2Labels := by
      have ha : raw42843step2 = raw42843step1 := by apply Matrix.ext; unfold raw42843step2 raw42843step1; decide +kernel
      have hl : raw42843step1Labels = labelEmbedding6 ∘ raw42843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42843step1 raw42843step1Labels raw42843step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

def raw42844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42844Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42844 raw42844Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw42844 raw42844Labels = mixedMoment B raw42844step0 raw42844step0Labels := by
      have ha : raw42844step0 = (fun i j => raw42844 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42844step0 raw42844; decide +kernel
      have hl : raw42844step0Labels = raw42844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42844 raw42844Labels permutation158 permutation2
    mixedMoment B raw42844step0 raw42844step0Labels = mixedMoment B raw42844step1 raw42844step1Labels := by
      have ha : raw42844step1 = raw42844step0 := by apply Matrix.ext; unfold raw42844step1 raw42844step0; decide +kernel
      have hl : raw42844step0Labels = labelEmbedding1 ∘ raw42844step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42844step0 raw42844step0Labels raw42844step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw42845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42845Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42845step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42845 raw42845Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw42845 raw42845Labels = mixedMoment B raw42845step0 raw42845step0Labels := by
      have ha : raw42845step0 = (fun i j => raw42845 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42845step0 raw42845; decide +kernel
      have hl : raw42845step0Labels = raw42845Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42845 raw42845Labels permutation166 permutation7
    mixedMoment B raw42845step0 raw42845step0Labels = mixedMoment B raw42845step1 raw42845step1Labels := by
      have ha : raw42845step1 = -raw42845step0 := by apply Matrix.ext; change ∀ i j, raw42845step1 i j = -(raw42845step0 i j); unfold raw42845step1 raw42845step0; decide +kernel
      have hl : raw42845step1Labels = raw42845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42845step1 raw42845step1Labels = mixedMoment B raw42845step2 raw42845step2Labels := by
      have ha : raw42845step2 = raw42845step1 := by apply Matrix.ext; unfold raw42845step2 raw42845step1; decide +kernel
      have hl : raw42845step1Labels = labelEmbedding6 ∘ raw42845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42845step1 raw42845step1Labels raw42845step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw42846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42846Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42846step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42846 raw42846Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw42846 raw42846Labels = mixedMoment B raw42846step0 raw42846step0Labels := by
      have hz : ∀ j, raw42846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42846step0 = (fun i j => raw42846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42846step0 raw42846; decide +kernel
      have hl : raw42846step0Labels = raw42846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42846 raw42846Labels permutation434 hz
    mixedMoment B raw42846step0 raw42846step0Labels = mixedMoment B raw42846step1 raw42846step1Labels := by
      have ha : raw42846step1 = raw42846step0 := by apply Matrix.ext; unfold raw42846step1 raw42846step0; decide +kernel
      have hl : raw42846step0Labels = labelEmbedding1 ∘ raw42846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42846step0 raw42846step0Labels raw42846step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw42847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42847Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42847step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw42847step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42847 raw42847Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw42847 raw42847Labels = mixedMoment B raw42847step0 raw42847step0Labels := by
      have hz : ∀ j, raw42847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42847step0 = (fun i j => raw42847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42847step0 raw42847; decide +kernel
      have hl : raw42847step0Labels = raw42847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42847 raw42847Labels permutation434 hz
    mixedMoment B raw42847step0 raw42847step0Labels = mixedMoment B raw42847step1 raw42847step1Labels := by
      have ha : raw42847step1 = (fun i j => raw42847step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42847step1 raw42847step0; decide +kernel
      have hl : raw42847step1Labels = raw42847step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42847step0 raw42847step0Labels permutation34 permutation7
    mixedMoment B raw42847step1 raw42847step1Labels = mixedMoment B raw42847step2 raw42847step2Labels := by
      have ha : raw42847step2 = -raw42847step1 := by apply Matrix.ext; change ∀ i j, raw42847step2 i j = -(raw42847step1 i j); unfold raw42847step2 raw42847step1; decide +kernel
      have hl : raw42847step2Labels = raw42847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42847step2 raw42847step2Labels = mixedMoment B raw42847step3 raw42847step3Labels := by
      have ha : raw42847step3 = raw42847step2 := by apply Matrix.ext; unfold raw42847step3 raw42847step2; decide +kernel
      have hl : raw42847step2Labels = labelEmbedding6 ∘ raw42847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42847step2 raw42847step2Labels raw42847step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw42848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42848Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42848 raw42848Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw42848 raw42848Labels = mixedMoment B raw42848step0 raw42848step0Labels := by
      have ha : raw42848step0 = (fun i j => raw42848 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42848step0 raw42848; decide +kernel
      have hl : raw42848step0Labels = raw42848Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42848 raw42848Labels permutation157 permutation2
    mixedMoment B raw42848step0 raw42848step0Labels = mixedMoment B raw42848step1 raw42848step1Labels := by
      have ha : raw42848step1 = raw42848step0 := by apply Matrix.ext; unfold raw42848step1 raw42848step0; decide +kernel
      have hl : raw42848step0Labels = labelEmbedding1 ∘ raw42848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42848step0 raw42848step0Labels raw42848step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw42849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42849Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw42849step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42849 raw42849Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw42849 raw42849Labels = mixedMoment B raw42849step0 raw42849step0Labels := by
      have ha : raw42849step0 = (fun i j => raw42849 (permutation174 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42849step0 raw42849; decide +kernel
      have hl : raw42849step0Labels = raw42849Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42849 raw42849Labels permutation174 permutation7
    mixedMoment B raw42849step0 raw42849step0Labels = mixedMoment B raw42849step1 raw42849step1Labels := by
      have ha : raw42849step1 = -raw42849step0 := by apply Matrix.ext; change ∀ i j, raw42849step1 i j = -(raw42849step0 i j); unfold raw42849step1 raw42849step0; decide +kernel
      have hl : raw42849step1Labels = raw42849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42849step1 raw42849step1Labels = mixedMoment B raw42849step2 raw42849step2Labels := by
      have ha : raw42849step2 = raw42849step1 := by apply Matrix.ext; unfold raw42849step2 raw42849step1; decide +kernel
      have hl : raw42849step1Labels = labelEmbedding6 ∘ raw42849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42849step1 raw42849step1Labels raw42849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw42850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42850Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42850 raw42850Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw42850 raw42850Labels = mixedMoment B raw42850step0 raw42850step0Labels := by
      have ha : raw42850step0 = raw42850 := by apply Matrix.ext; unfold raw42850step0 raw42850; decide +kernel
      have hl : raw42850Labels = labelEmbedding1 ∘ raw42850step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42850 raw42850Labels raw42850step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw42851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42851Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw42851step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw42851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42851 raw42851Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw42851 raw42851Labels = mixedMoment B raw42851step0 raw42851step0Labels := by
      have ha : raw42851step0 = (fun i j => raw42851 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42851step0 raw42851; decide +kernel
      have hl : raw42851step0Labels = raw42851Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42851 raw42851Labels permutation164 permutation7
    mixedMoment B raw42851step0 raw42851step0Labels = mixedMoment B raw42851step1 raw42851step1Labels := by
      have ha : raw42851step1 = -raw42851step0 := by apply Matrix.ext; change ∀ i j, raw42851step1 i j = -(raw42851step0 i j); unfold raw42851step1 raw42851step0; decide +kernel
      have hl : raw42851step1Labels = raw42851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42851step1 raw42851step1Labels = mixedMoment B raw42851step2 raw42851step2Labels := by
      have ha : raw42851step2 = raw42851step1 := by apply Matrix.ext; unfold raw42851step2 raw42851step1; decide +kernel
      have hl : raw42851step1Labels = labelEmbedding6 ∘ raw42851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42851step1 raw42851step1Labels raw42851step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4527 node4527Labels := by rfl

def raw42852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42852Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42852 raw42852Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw42852 raw42852Labels = mixedMoment B raw42852step0 raw42852step0Labels := by
      have hz : ∀ j, raw42852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42852step0 = (fun i j => raw42852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42852step0 raw42852; decide +kernel
      have hl : raw42852step0Labels = raw42852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42852 raw42852Labels permutation434 hz
    mixedMoment B raw42852step0 raw42852step0Labels = mixedMoment B raw42852step1 raw42852step1Labels := by
      have ha : raw42852step1 = raw42852step0 := by apply Matrix.ext; unfold raw42852step1 raw42852step0; decide +kernel
      have hl : raw42852step0Labels = labelEmbedding1 ∘ raw42852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42852step0 raw42852step0Labels raw42852step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

def raw42853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42853Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42853step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42853 raw42853Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw42853 raw42853Labels = mixedMoment B raw42853step0 raw42853step0Labels := by
      have hz : ∀ j, raw42853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42853step0 = (fun i j => raw42853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42853step0 raw42853; decide +kernel
      have hl : raw42853step0Labels = raw42853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42853 raw42853Labels permutation434 hz
    mixedMoment B raw42853step0 raw42853step0Labels = mixedMoment B raw42853step1 raw42853step1Labels := by
      have ha : raw42853step1 = (fun i j => raw42853step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42853step1 raw42853step0; decide +kernel
      have hl : raw42853step1Labels = raw42853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42853step0 raw42853step0Labels permutation145 permutation6
    _ = mixedMoment B node4531 node4531Labels := by rfl

def raw42854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42854Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42854 raw42854Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw42854 raw42854Labels = mixedMoment B raw42854step0 raw42854step0Labels := by
      have ha : raw42854step0 = (fun i j => raw42854 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42854step0 raw42854; decide +kernel
      have hl : raw42854step0Labels = raw42854Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42854 raw42854Labels permutation157 permutation2
    mixedMoment B raw42854step0 raw42854step0Labels = mixedMoment B raw42854step1 raw42854step1Labels := by
      have ha : raw42854step1 = raw42854step0 := by apply Matrix.ext; unfold raw42854step1 raw42854step0; decide +kernel
      have hl : raw42854step0Labels = labelEmbedding1 ∘ raw42854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42854step0 raw42854step0Labels raw42854step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw42855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42855Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw42855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42855 raw42855Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw42855 raw42855Labels = mixedMoment B raw42855step0 raw42855step0Labels := by
      have ha : raw42855step0 = (fun i j => raw42855 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42855step0 raw42855; decide +kernel
      have hl : raw42855step0Labels = raw42855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42855 raw42855Labels permutation171 permutation7
    mixedMoment B raw42855step0 raw42855step0Labels = mixedMoment B raw42855step1 raw42855step1Labels := by
      have ha : raw42855step1 = -raw42855step0 := by apply Matrix.ext; change ∀ i j, raw42855step1 i j = -(raw42855step0 i j); unfold raw42855step1 raw42855step0; decide +kernel
      have hl : raw42855step1Labels = raw42855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42855step1 raw42855step1Labels = mixedMoment B raw42855step2 raw42855step2Labels := by
      have ha : raw42855step2 = raw42855step1 := by apply Matrix.ext; unfold raw42855step2 raw42855step1; decide +kernel
      have hl : raw42855step1Labels = labelEmbedding6 ∘ raw42855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42855step1 raw42855step1Labels raw42855step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw42856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42856Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42856 raw42856Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw42856 raw42856Labels = mixedMoment B raw42856step0 raw42856step0Labels := by
      have ha : raw42856step0 = (fun i j => raw42856 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42856step0 raw42856; decide +kernel
      have hl : raw42856step0Labels = raw42856Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42856 raw42856Labels permutation156 permutation2
    mixedMoment B raw42856step0 raw42856step0Labels = mixedMoment B raw42856step1 raw42856step1Labels := by
      have ha : raw42856step1 = raw42856step0 := by apply Matrix.ext; unfold raw42856step1 raw42856step0; decide +kernel
      have hl : raw42856step0Labels = labelEmbedding1 ∘ raw42856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42856step0 raw42856step0Labels raw42856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw42857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42857Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw42857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42857 raw42857Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw42857 raw42857Labels = mixedMoment B raw42857step0 raw42857step0Labels := by
      have ha : raw42857step0 = (fun i j => raw42857 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42857step0 raw42857; decide +kernel
      have hl : raw42857step0Labels = raw42857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42857 raw42857Labels permutation170 permutation7
    mixedMoment B raw42857step0 raw42857step0Labels = mixedMoment B raw42857step1 raw42857step1Labels := by
      have ha : raw42857step1 = -raw42857step0 := by apply Matrix.ext; change ∀ i j, raw42857step1 i j = -(raw42857step0 i j); unfold raw42857step1 raw42857step0; decide +kernel
      have hl : raw42857step1Labels = raw42857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42857step1 raw42857step1Labels = mixedMoment B raw42857step2 raw42857step2Labels := by
      have ha : raw42857step2 = raw42857step1 := by apply Matrix.ext; unfold raw42857step2 raw42857step1; decide +kernel
      have hl : raw42857step1Labels = labelEmbedding6 ∘ raw42857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42857step1 raw42857step1Labels raw42857step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw42858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42858Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42858step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42858step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42858step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42858 raw42858Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw42858 raw42858Labels = mixedMoment B raw42858step0 raw42858step0Labels := by
      have hz : ∀ j, raw42858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42858step0 = (fun i j => raw42858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42858step0 raw42858; decide +kernel
      have hl : raw42858step0Labels = raw42858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42858 raw42858Labels permutation434 hz
    mixedMoment B raw42858step0 raw42858step0Labels = mixedMoment B raw42858step1 raw42858step1Labels := by
      have hz : ∀ j, raw42858step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42858step1 = (fun i j => raw42858step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42858step1 raw42858step0; decide +kernel
      have hl : raw42858step1Labels = raw42858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42858step0 raw42858step0Labels permutation80 hz
    mixedMoment B raw42858step1 raw42858step1Labels = mixedMoment B raw42858step2 raw42858step2Labels := by
      have ha : raw42858step2 = (fun i j => raw42858step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42858step2 raw42858step1; decide +kernel
      have hl : raw42858step2Labels = raw42858step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42858step1 raw42858step1Labels permutation29 permutation4
    mixedMoment B raw42858step2 raw42858step2Labels = mixedMoment B raw42858step3 raw42858step3Labels := by
      have ha : raw42858step3 = -raw42858step2 := by apply Matrix.ext; change ∀ i j, raw42858step3 i j = -(raw42858step2 i j); unfold raw42858step3 raw42858step2; decide +kernel
      have hl : raw42858step3Labels = raw42858step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42858step3 raw42858step3Labels = mixedMoment B raw42858step4 raw42858step4Labels := by
      have ha : raw42858step4 = raw42858step3 := by apply Matrix.ext; unfold raw42858step4 raw42858step3; decide +kernel
      have hl : raw42858step3Labels = labelEmbedding1 ∘ raw42858step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42858step3 raw42858step3Labels raw42858step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw42859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42859Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42859step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42859step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42859 raw42859Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw42859 raw42859Labels = mixedMoment B raw42859step0 raw42859step0Labels := by
      have hz : ∀ j, raw42859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42859step0 = (fun i j => raw42859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42859step0 raw42859; decide +kernel
      have hl : raw42859step0Labels = raw42859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42859 raw42859Labels permutation434 hz
    mixedMoment B raw42859step0 raw42859step0Labels = mixedMoment B raw42859step1 raw42859step1Labels := by
      have hz : ∀ j, raw42859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42859step1 = (fun i j => raw42859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42859step1 raw42859step0; decide +kernel
      have hl : raw42859step1Labels = raw42859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42859step0 raw42859step0Labels permutation80 hz
    mixedMoment B raw42859step1 raw42859step1Labels = mixedMoment B raw42859step2 raw42859step2Labels := by
      have ha : raw42859step2 = (fun i j => raw42859step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42859step2 raw42859step1; decide +kernel
      have hl : raw42859step2Labels = raw42859step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42859step1 raw42859step1Labels permutation31 permutation6
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw42860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42860Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw42860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42860 raw42860Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw42860 raw42860Labels = mixedMoment B raw42860step0 raw42860step0Labels := by
      have hz : ∀ j, raw42860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42860step0 = (fun i j => raw42860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42860step0 raw42860; decide +kernel
      have hl : raw42860step0Labels = raw42860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42860 raw42860Labels permutation346 hz
    mixedMoment B raw42860step0 raw42860step0Labels = mixedMoment B raw42860step1 raw42860step1Labels := by
      have ha : raw42860step1 = (fun i j => raw42860step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42860step1 raw42860step0; decide +kernel
      have hl : raw42860step1Labels = raw42860step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42860step0 raw42860step0Labels permutation95 permutation4
    mixedMoment B raw42860step1 raw42860step1Labels = mixedMoment B raw42860step2 raw42860step2Labels := by
      have ha : raw42860step2 = -raw42860step1 := by apply Matrix.ext; change ∀ i j, raw42860step2 i j = -(raw42860step1 i j); unfold raw42860step2 raw42860step1; decide +kernel
      have hl : raw42860step2Labels = raw42860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42860step2 raw42860step2Labels = mixedMoment B raw42860step3 raw42860step3Labels := by
      have ha : raw42860step3 = raw42860step2 := by apply Matrix.ext; unfold raw42860step3 raw42860step2; decide +kernel
      have hl : raw42860step2Labels = labelEmbedding1 ∘ raw42860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42860step2 raw42860step2Labels raw42860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw42861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42861Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42861step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw42861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42861 raw42861Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw42861 raw42861Labels = mixedMoment B raw42861step0 raw42861step0Labels := by
      have hz : ∀ j, raw42861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42861step0 = (fun i j => raw42861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42861step0 raw42861; decide +kernel
      have hl : raw42861step0Labels = raw42861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42861 raw42861Labels permutation346 hz
    mixedMoment B raw42861step0 raw42861step0Labels = mixedMoment B raw42861step1 raw42861step1Labels := by
      have ha : raw42861step1 = (fun i j => raw42861step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42861step1 raw42861step0; decide +kernel
      have hl : raw42861step1Labels = raw42861step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42861step0 raw42861step0Labels permutation97 permutation6
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw42862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42862Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw42862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42862 raw42862Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw42862 raw42862Labels = mixedMoment B raw42862step0 raw42862step0Labels := by
      have hz : ∀ j, raw42862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42862step0 = (fun i j => raw42862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42862step0 raw42862; decide +kernel
      have hl : raw42862step0Labels = raw42862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42862 raw42862Labels permutation346 hz
    mixedMoment B raw42862step0 raw42862step0Labels = mixedMoment B raw42862step1 raw42862step1Labels := by
      have ha : raw42862step1 = (fun i j => raw42862step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42862step1 raw42862step0; decide +kernel
      have hl : raw42862step1Labels = raw42862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42862step0 raw42862step0Labels permutation37 permutation2
    mixedMoment B raw42862step1 raw42862step1Labels = mixedMoment B raw42862step2 raw42862step2Labels := by
      have ha : raw42862step2 = raw42862step1 := by apply Matrix.ext; unfold raw42862step2 raw42862step1; decide +kernel
      have hl : raw42862step1Labels = labelEmbedding1 ∘ raw42862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42862step1 raw42862step1Labels raw42862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw42863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42863Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42863step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw42863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42863step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw42863step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42863 raw42863Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw42863 raw42863Labels = mixedMoment B raw42863step0 raw42863step0Labels := by
      have hz : ∀ j, raw42863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42863step0 = (fun i j => raw42863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42863step0 raw42863; decide +kernel
      have hl : raw42863step0Labels = raw42863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42863 raw42863Labels permutation346 hz
    mixedMoment B raw42863step0 raw42863step0Labels = mixedMoment B raw42863step1 raw42863step1Labels := by
      have ha : raw42863step1 = (fun i j => raw42863step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42863step1 raw42863step0; decide +kernel
      have hl : raw42863step1Labels = raw42863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42863step0 raw42863step0Labels permutation37 permutation7
    mixedMoment B raw42863step1 raw42863step1Labels = mixedMoment B raw42863step2 raw42863step2Labels := by
      have ha : raw42863step2 = -raw42863step1 := by apply Matrix.ext; change ∀ i j, raw42863step2 i j = -(raw42863step1 i j); unfold raw42863step2 raw42863step1; decide +kernel
      have hl : raw42863step2Labels = raw42863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42863step2 raw42863step2Labels = mixedMoment B raw42863step3 raw42863step3Labels := by
      have ha : raw42863step3 = raw42863step2 := by apply Matrix.ext; unfold raw42863step3 raw42863step2; decide +kernel
      have hl : raw42863step2Labels = labelEmbedding6 ∘ raw42863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42863step2 raw42863step2Labels raw42863step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw42864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42864Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]
def raw42864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw42864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42864 raw42864Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw42864 raw42864Labels = mixedMoment B raw42864step0 raw42864step0Labels := by
      have hz : ∀ j, raw42864 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42864step0 = (fun i j => raw42864 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42864step0 raw42864; decide +kernel
      have hl : raw42864step0Labels = raw42864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42864 raw42864Labels permutation520 hz
    mixedMoment B raw42864step0 raw42864step0Labels = mixedMoment B raw42864step1 raw42864step1Labels := by
      have hz : ∀ j, raw42864step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42864step1 = (fun i j => raw42864step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42864step1 raw42864step0; decide +kernel
      have hl : raw42864step1Labels = raw42864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42864step0 raw42864step0Labels permutation104 hz
    mixedMoment B raw42864step1 raw42864step1Labels = mixedMoment B raw42864step2 raw42864step2Labels := by
      have ha : raw42864step2 = (fun i j => raw42864step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42864step2 raw42864step1; decide +kernel
      have hl : raw42864step2Labels = raw42864step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42864step1 raw42864step1Labels permutation8 permutation4
    mixedMoment B raw42864step2 raw42864step2Labels = mixedMoment B raw42864step3 raw42864step3Labels := by
      have ha : raw42864step3 = -raw42864step2 := by apply Matrix.ext; change ∀ i j, raw42864step3 i j = -(raw42864step2 i j); unfold raw42864step3 raw42864step2; decide +kernel
      have hl : raw42864step3Labels = raw42864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42864step3 raw42864step3Labels = mixedMoment B raw42864step4 raw42864step4Labels := by
      have ha : raw42864step4 = raw42864step3 := by apply Matrix.ext; unfold raw42864step4 raw42864step3; decide +kernel
      have hl : raw42864step3Labels = labelEmbedding1 ∘ raw42864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42864step3 raw42864step3Labels raw42864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw42865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42865Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw42865step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0]]
def raw42865step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42865step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42865step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42865 raw42865Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw42865 raw42865Labels = mixedMoment B raw42865step0 raw42865step0Labels := by
      have hz : ∀ j, raw42865 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42865step0 = (fun i j => raw42865 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42865step0 raw42865; decide +kernel
      have hl : raw42865step0Labels = raw42865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42865 raw42865Labels permutation520 hz
    mixedMoment B raw42865step0 raw42865step0Labels = mixedMoment B raw42865step1 raw42865step1Labels := by
      have hz : ∀ j, raw42865step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42865step1 = (fun i j => raw42865step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42865step1 raw42865step0; decide +kernel
      have hl : raw42865step1Labels = raw42865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42865step0 raw42865step0Labels permutation104 hz
    mixedMoment B raw42865step1 raw42865step1Labels = mixedMoment B raw42865step2 raw42865step2Labels := by
      have ha : raw42865step2 = (fun i j => raw42865step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42865step2 raw42865step1; decide +kernel
      have hl : raw42865step2Labels = raw42865step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42865step1 raw42865step1Labels permutation29 permutation5
    mixedMoment B raw42865step2 raw42865step2Labels = mixedMoment B raw42865step3 raw42865step3Labels := by
      have ha : raw42865step3 = raw42865step2 := by apply Matrix.ext; unfold raw42865step3 raw42865step2; decide +kernel
      have hl : raw42865step2Labels = labelEmbedding9 ∘ raw42865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42865step2 raw42865step2Labels raw42865step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw42866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42866Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42866 raw42866Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw42866 raw42866Labels = mixedMoment B raw42866step0 raw42866step0Labels := by
      have hz : ∀ j, raw42866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42866step0 = (fun i j => raw42866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42866step0 raw42866; decide +kernel
      have hl : raw42866step0Labels = raw42866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42866 raw42866Labels permutation434 hz
    mixedMoment B raw42866step0 raw42866step0Labels = mixedMoment B raw42866step1 raw42866step1Labels := by
      have ha : raw42866step1 = (fun i j => raw42866step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42866step1 raw42866step0; decide +kernel
      have hl : raw42866step1Labels = raw42866step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42866step0 raw42866step0Labels permutation32 permutation4
    mixedMoment B raw42866step1 raw42866step1Labels = mixedMoment B raw42866step2 raw42866step2Labels := by
      have ha : raw42866step2 = -raw42866step1 := by apply Matrix.ext; change ∀ i j, raw42866step2 i j = -(raw42866step1 i j); unfold raw42866step2 raw42866step1; decide +kernel
      have hl : raw42866step2Labels = raw42866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42866step2 raw42866step2Labels = mixedMoment B raw42866step3 raw42866step3Labels := by
      have ha : raw42866step3 = raw42866step2 := by apply Matrix.ext; unfold raw42866step3 raw42866step2; decide +kernel
      have hl : raw42866step2Labels = labelEmbedding1 ∘ raw42866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42866step2 raw42866step2Labels raw42866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw42867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42867Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42867step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42867step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42867 raw42867Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw42867 raw42867Labels = mixedMoment B raw42867step0 raw42867step0Labels := by
      have hz : ∀ j, raw42867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42867step0 = (fun i j => raw42867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42867step0 raw42867; decide +kernel
      have hl : raw42867step0Labels = raw42867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42867 raw42867Labels permutation434 hz
    mixedMoment B raw42867step0 raw42867step0Labels = mixedMoment B raw42867step1 raw42867step1Labels := by
      have ha : raw42867step1 = (fun i j => raw42867step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42867step1 raw42867step0; decide +kernel
      have hl : raw42867step1Labels = raw42867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42867step0 raw42867step0Labels permutation32 permutation4
    mixedMoment B raw42867step1 raw42867step1Labels = mixedMoment B raw42867step2 raw42867step2Labels := by
      have ha : raw42867step2 = -raw42867step1 := by apply Matrix.ext; change ∀ i j, raw42867step2 i j = -(raw42867step1 i j); unfold raw42867step2 raw42867step1; decide +kernel
      have hl : raw42867step2Labels = raw42867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42867step2 raw42867step2Labels = mixedMoment B raw42867step3 raw42867step3Labels := by
      have ha : raw42867step3 = raw42867step2 := by apply Matrix.ext; unfold raw42867step3 raw42867step2; decide +kernel
      have hl : raw42867step2Labels = labelEmbedding10 ∘ raw42867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42867step2 raw42867step2Labels raw42867step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw42868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42868Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42868step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42868 raw42868Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw42868 raw42868Labels = mixedMoment B raw42868step0 raw42868step0Labels := by
      have hz : ∀ j, raw42868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42868step0 = (fun i j => raw42868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42868step0 raw42868; decide +kernel
      have hl : raw42868step0Labels = raw42868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42868 raw42868Labels permutation434 hz
    mixedMoment B raw42868step0 raw42868step0Labels = mixedMoment B raw42868step1 raw42868step1Labels := by
      have ha : raw42868step1 = (fun i j => raw42868step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42868step1 raw42868step0; decide +kernel
      have hl : raw42868step1Labels = raw42868step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42868step0 raw42868step0Labels permutation33 permutation4
    mixedMoment B raw42868step1 raw42868step1Labels = mixedMoment B raw42868step2 raw42868step2Labels := by
      have ha : raw42868step2 = -raw42868step1 := by apply Matrix.ext; change ∀ i j, raw42868step2 i j = -(raw42868step1 i j); unfold raw42868step2 raw42868step1; decide +kernel
      have hl : raw42868step2Labels = raw42868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42868step2 raw42868step2Labels = mixedMoment B raw42868step3 raw42868step3Labels := by
      have ha : raw42868step3 = raw42868step2 := by apply Matrix.ext; unfold raw42868step3 raw42868step2; decide +kernel
      have hl : raw42868step2Labels = labelEmbedding1 ∘ raw42868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42868step2 raw42868step2Labels raw42868step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw42869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42869Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42869step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42869step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42869 raw42869Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42869 raw42869Labels = mixedMoment B raw42869step0 raw42869step0Labels := by
      have hz : ∀ j, raw42869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42869step0 = (fun i j => raw42869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42869step0 raw42869; decide +kernel
      have hl : raw42869step0Labels = raw42869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42869 raw42869Labels permutation434 hz
    mixedMoment B raw42869step0 raw42869step0Labels = mixedMoment B raw42869step1 raw42869step1Labels := by
      have ha : raw42869step1 = (fun i j => raw42869step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42869step1 raw42869step0; decide +kernel
      have hl : raw42869step1Labels = raw42869step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42869step0 raw42869step0Labels permutation33 permutation4
    mixedMoment B raw42869step1 raw42869step1Labels = mixedMoment B raw42869step2 raw42869step2Labels := by
      have ha : raw42869step2 = -raw42869step1 := by apply Matrix.ext; change ∀ i j, raw42869step2 i j = -(raw42869step1 i j); unfold raw42869step2 raw42869step1; decide +kernel
      have hl : raw42869step2Labels = raw42869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42869step2 raw42869step2Labels = mixedMoment B raw42869step3 raw42869step3Labels := by
      have ha : raw42869step3 = raw42869step2 := by apply Matrix.ext; unfold raw42869step3 raw42869step2; decide +kernel
      have hl : raw42869step2Labels = labelEmbedding10 ∘ raw42869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42869step2 raw42869step2Labels raw42869step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42870Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42870 raw42870Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw42870 raw42870Labels = mixedMoment B raw42870step0 raw42870step0Labels := by
      have ha : raw42870step0 = (fun i j => raw42870 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42870step0 raw42870; decide +kernel
      have hl : raw42870step0Labels = raw42870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42870 raw42870Labels permutation224 permutation4
    mixedMoment B raw42870step0 raw42870step0Labels = mixedMoment B raw42870step1 raw42870step1Labels := by
      have ha : raw42870step1 = -raw42870step0 := by apply Matrix.ext; change ∀ i j, raw42870step1 i j = -(raw42870step0 i j); unfold raw42870step1 raw42870step0; decide +kernel
      have hl : raw42870step1Labels = raw42870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42870step1 raw42870step1Labels = mixedMoment B raw42870step2 raw42870step2Labels := by
      have ha : raw42870step2 = raw42870step1 := by apply Matrix.ext; unfold raw42870step2 raw42870step1; decide +kernel
      have hl : raw42870step1Labels = labelEmbedding1 ∘ raw42870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42870step1 raw42870step1Labels raw42870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw42871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42871Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42871step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42871step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42871 raw42871Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42871 raw42871Labels = mixedMoment B raw42871step0 raw42871step0Labels := by
      have ha : raw42871step0 = (fun i j => raw42871 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42871step0 raw42871; decide +kernel
      have hl : raw42871step0Labels = raw42871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42871 raw42871Labels permutation224 permutation4
    mixedMoment B raw42871step0 raw42871step0Labels = mixedMoment B raw42871step1 raw42871step1Labels := by
      have ha : raw42871step1 = -raw42871step0 := by apply Matrix.ext; change ∀ i j, raw42871step1 i j = -(raw42871step0 i j); unfold raw42871step1 raw42871step0; decide +kernel
      have hl : raw42871step1Labels = raw42871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42871step1 raw42871step1Labels = mixedMoment B raw42871step2 raw42871step2Labels := by
      have ha : raw42871step2 = raw42871step1 := by apply Matrix.ext; unfold raw42871step2 raw42871step1; decide +kernel
      have hl : raw42871step1Labels = labelEmbedding10 ∘ raw42871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42871step1 raw42871step1Labels raw42871step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42872Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42872step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42872 raw42872Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw42872 raw42872Labels = mixedMoment B raw42872step0 raw42872step0Labels := by
      have ha : raw42872step0 = (fun i j => raw42872 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42872step0 raw42872; decide +kernel
      have hl : raw42872step0Labels = raw42872Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42872 raw42872Labels permutation246 permutation4
    mixedMoment B raw42872step0 raw42872step0Labels = mixedMoment B raw42872step1 raw42872step1Labels := by
      have ha : raw42872step1 = -raw42872step0 := by apply Matrix.ext; change ∀ i j, raw42872step1 i j = -(raw42872step0 i j); unfold raw42872step1 raw42872step0; decide +kernel
      have hl : raw42872step1Labels = raw42872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42872step1 raw42872step1Labels = mixedMoment B raw42872step2 raw42872step2Labels := by
      have ha : raw42872step2 = raw42872step1 := by apply Matrix.ext; unfold raw42872step2 raw42872step1; decide +kernel
      have hl : raw42872step1Labels = labelEmbedding1 ∘ raw42872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42872step1 raw42872step1Labels raw42872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw42873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42873Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42873step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42873step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42873 raw42873Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw42873 raw42873Labels = mixedMoment B raw42873step0 raw42873step0Labels := by
      have ha : raw42873step0 = (fun i j => raw42873 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42873step0 raw42873; decide +kernel
      have hl : raw42873step0Labels = raw42873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42873 raw42873Labels permutation246 permutation4
    mixedMoment B raw42873step0 raw42873step0Labels = mixedMoment B raw42873step1 raw42873step1Labels := by
      have ha : raw42873step1 = -raw42873step0 := by apply Matrix.ext; change ∀ i j, raw42873step1 i j = -(raw42873step0 i j); unfold raw42873step1 raw42873step0; decide +kernel
      have hl : raw42873step1Labels = raw42873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42873step1 raw42873step1Labels = mixedMoment B raw42873step2 raw42873step2Labels := by
      have ha : raw42873step2 = raw42873step1 := by apply Matrix.ext; unfold raw42873step2 raw42873step1; decide +kernel
      have hl : raw42873step1Labels = labelEmbedding10 ∘ raw42873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42873step1 raw42873step1Labels raw42873step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw42874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42874Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42874 raw42874Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw42874 raw42874Labels = mixedMoment B raw42874step0 raw42874step0Labels := by
      have ha : raw42874step0 = (fun i j => raw42874 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42874step0 raw42874; decide +kernel
      have hl : raw42874step0Labels = raw42874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42874 raw42874Labels permutation247 permutation4
    mixedMoment B raw42874step0 raw42874step0Labels = mixedMoment B raw42874step1 raw42874step1Labels := by
      have ha : raw42874step1 = -raw42874step0 := by apply Matrix.ext; change ∀ i j, raw42874step1 i j = -(raw42874step0 i j); unfold raw42874step1 raw42874step0; decide +kernel
      have hl : raw42874step1Labels = raw42874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42874step1 raw42874step1Labels = mixedMoment B raw42874step2 raw42874step2Labels := by
      have ha : raw42874step2 = raw42874step1 := by apply Matrix.ext; unfold raw42874step2 raw42874step1; decide +kernel
      have hl : raw42874step1Labels = labelEmbedding1 ∘ raw42874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42874step1 raw42874step1Labels raw42874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw42875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42875Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42875step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42875step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42875 raw42875Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw42875 raw42875Labels = mixedMoment B raw42875step0 raw42875step0Labels := by
      have ha : raw42875step0 = (fun i j => raw42875 (permutation247 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42875step0 raw42875; decide +kernel
      have hl : raw42875step0Labels = raw42875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42875 raw42875Labels permutation247 permutation4
    mixedMoment B raw42875step0 raw42875step0Labels = mixedMoment B raw42875step1 raw42875step1Labels := by
      have ha : raw42875step1 = -raw42875step0 := by apply Matrix.ext; change ∀ i j, raw42875step1 i j = -(raw42875step0 i j); unfold raw42875step1 raw42875step0; decide +kernel
      have hl : raw42875step1Labels = raw42875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42875step1 raw42875step1Labels = mixedMoment B raw42875step2 raw42875step2Labels := by
      have ha : raw42875step2 = raw42875step1 := by apply Matrix.ext; unfold raw42875step2 raw42875step1; decide +kernel
      have hl : raw42875step1Labels = labelEmbedding10 ∘ raw42875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42875step1 raw42875step1Labels raw42875step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw42876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42876Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42876step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42876step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42876step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42876 raw42876Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw42876 raw42876Labels = mixedMoment B raw42876step0 raw42876step0Labels := by
      have hz : ∀ j, raw42876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42876step0 = (fun i j => raw42876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42876step0 raw42876; decide +kernel
      have hl : raw42876step0Labels = raw42876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42876 raw42876Labels permutation434 hz
    mixedMoment B raw42876step0 raw42876step0Labels = mixedMoment B raw42876step1 raw42876step1Labels := by
      have ha : raw42876step1 = (fun i j => raw42876step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42876step1 raw42876step0; decide +kernel
      have hl : raw42876step1Labels = raw42876step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42876step0 raw42876step0Labels permutation44 permutation4
    mixedMoment B raw42876step1 raw42876step1Labels = mixedMoment B raw42876step2 raw42876step2Labels := by
      have ha : raw42876step2 = -raw42876step1 := by apply Matrix.ext; change ∀ i j, raw42876step2 i j = -(raw42876step1 i j); unfold raw42876step2 raw42876step1; decide +kernel
      have hl : raw42876step2Labels = raw42876step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42876step2 raw42876step2Labels = mixedMoment B raw42876step3 raw42876step3Labels := by
      have ha : raw42876step3 = raw42876step2 := by apply Matrix.ext; unfold raw42876step3 raw42876step2; decide +kernel
      have hl : raw42876step2Labels = labelEmbedding1 ∘ raw42876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42876step2 raw42876step2Labels raw42876step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw42877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42877Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42877step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42877step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42877step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42877 raw42877Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42877 raw42877Labels = mixedMoment B raw42877step0 raw42877step0Labels := by
      have hz : ∀ j, raw42877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42877step0 = (fun i j => raw42877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42877step0 raw42877; decide +kernel
      have hl : raw42877step0Labels = raw42877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42877 raw42877Labels permutation434 hz
    mixedMoment B raw42877step0 raw42877step0Labels = mixedMoment B raw42877step1 raw42877step1Labels := by
      have ha : raw42877step1 = (fun i j => raw42877step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42877step1 raw42877step0; decide +kernel
      have hl : raw42877step1Labels = raw42877step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42877step0 raw42877step0Labels permutation44 permutation4
    mixedMoment B raw42877step1 raw42877step1Labels = mixedMoment B raw42877step2 raw42877step2Labels := by
      have ha : raw42877step2 = -raw42877step1 := by apply Matrix.ext; change ∀ i j, raw42877step2 i j = -(raw42877step1 i j); unfold raw42877step2 raw42877step1; decide +kernel
      have hl : raw42877step2Labels = raw42877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42877step2 raw42877step2Labels = mixedMoment B raw42877step3 raw42877step3Labels := by
      have ha : raw42877step3 = raw42877step2 := by apply Matrix.ext; unfold raw42877step3 raw42877step2; decide +kernel
      have hl : raw42877step2Labels = labelEmbedding10 ∘ raw42877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42877step2 raw42877step2Labels raw42877step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42878Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42878 raw42878Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw42878 raw42878Labels = mixedMoment B raw42878step0 raw42878step0Labels := by
      have hz : ∀ j, raw42878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42878step0 = (fun i j => raw42878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42878step0 raw42878; decide +kernel
      have hl : raw42878step0Labels = raw42878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42878 raw42878Labels permutation434 hz
    mixedMoment B raw42878step0 raw42878step0Labels = mixedMoment B raw42878step1 raw42878step1Labels := by
      have ha : raw42878step1 = (fun i j => raw42878step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42878step1 raw42878step0; decide +kernel
      have hl : raw42878step1Labels = raw42878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42878step0 raw42878step0Labels permutation37 permutation4
    mixedMoment B raw42878step1 raw42878step1Labels = mixedMoment B raw42878step2 raw42878step2Labels := by
      have ha : raw42878step2 = -raw42878step1 := by apply Matrix.ext; change ∀ i j, raw42878step2 i j = -(raw42878step1 i j); unfold raw42878step2 raw42878step1; decide +kernel
      have hl : raw42878step2Labels = raw42878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42878step2 raw42878step2Labels = mixedMoment B raw42878step3 raw42878step3Labels := by
      have ha : raw42878step3 = raw42878step2 := by apply Matrix.ext; unfold raw42878step3 raw42878step2; decide +kernel
      have hl : raw42878step2Labels = labelEmbedding1 ∘ raw42878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42878step2 raw42878step2Labels raw42878step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw42879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42879Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42879step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42879step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42879step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42879step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42879 raw42879Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42879 raw42879Labels = mixedMoment B raw42879step0 raw42879step0Labels := by
      have hz : ∀ j, raw42879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42879step0 = (fun i j => raw42879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42879step0 raw42879; decide +kernel
      have hl : raw42879step0Labels = raw42879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42879 raw42879Labels permutation434 hz
    mixedMoment B raw42879step0 raw42879step0Labels = mixedMoment B raw42879step1 raw42879step1Labels := by
      have ha : raw42879step1 = (fun i j => raw42879step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42879step1 raw42879step0; decide +kernel
      have hl : raw42879step1Labels = raw42879step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42879step0 raw42879step0Labels permutation37 permutation4
    mixedMoment B raw42879step1 raw42879step1Labels = mixedMoment B raw42879step2 raw42879step2Labels := by
      have ha : raw42879step2 = -raw42879step1 := by apply Matrix.ext; change ∀ i j, raw42879step2 i j = -(raw42879step1 i j); unfold raw42879step2 raw42879step1; decide +kernel
      have hl : raw42879step2Labels = raw42879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42879step2 raw42879step2Labels = mixedMoment B raw42879step3 raw42879step3Labels := by
      have ha : raw42879step3 = raw42879step2 := by apply Matrix.ext; unfold raw42879step3 raw42879step2; decide +kernel
      have hl : raw42879step2Labels = labelEmbedding10 ∘ raw42879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42879step2 raw42879step2Labels raw42879step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
