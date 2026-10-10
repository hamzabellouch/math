import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8704step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8704step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8704 raw8704Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw8704 raw8704Labels = mixedMoment B raw8704step0 raw8704step0Labels := by
      have hz : ∀ j, raw8704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8704step0 = (fun i j => raw8704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8704step0 raw8704; decide +kernel
      have hl : raw8704step0Labels = raw8704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8704 raw8704Labels permutation346 hz
    mixedMoment B raw8704step0 raw8704step0Labels = mixedMoment B raw8704step1 raw8704step1Labels := by
      have hz : ∀ j, raw8704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8704step1 = (fun i j => raw8704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8704step1 raw8704step0; decide +kernel
      have hl : raw8704step1Labels = raw8704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8704step0 raw8704step0Labels permutation56 hz
    mixedMoment B raw8704step1 raw8704step1Labels = mixedMoment B raw8704step2 raw8704step2Labels := by
      have ha : raw8704step2 = (fun i j => raw8704step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8704step2 raw8704step1; decide +kernel
      have hl : raw8704step2Labels = raw8704step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8704step1 raw8704step1Labels permutation9 permutation3
    mixedMoment B raw8704step2 raw8704step2Labels = mixedMoment B raw8704step3 raw8704step3Labels := by
      have ha : raw8704step3 = raw8704step2 := by apply Matrix.ext; unfold raw8704step3 raw8704step2; decide +kernel
      have hl : raw8704step2Labels = labelEmbedding6 ∘ raw8704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8704step2 raw8704step2Labels raw8704step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw8705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8705step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8705step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8705 raw8705Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw8705 raw8705Labels = mixedMoment B raw8705step0 raw8705step0Labels := by
      have hz : ∀ j, raw8705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8705step0 = (fun i j => raw8705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8705step0 raw8705; decide +kernel
      have hl : raw8705step0Labels = raw8705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8705 raw8705Labels permutation346 hz
    mixedMoment B raw8705step0 raw8705step0Labels = mixedMoment B raw8705step1 raw8705step1Labels := by
      have hz : ∀ j, raw8705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8705step1 = (fun i j => raw8705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8705step1 raw8705step0; decide +kernel
      have hl : raw8705step1Labels = raw8705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8705step0 raw8705step0Labels permutation56 hz
    mixedMoment B raw8705step1 raw8705step1Labels = mixedMoment B raw8705step2 raw8705step2Labels := by
      have ha : raw8705step2 = (fun i j => raw8705step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8705step2 raw8705step1; decide +kernel
      have hl : raw8705step2Labels = raw8705step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8705step1 raw8705step1Labels permutation8 permutation3
    mixedMoment B raw8705step2 raw8705step2Labels = mixedMoment B raw8705step3 raw8705step3Labels := by
      have ha : raw8705step3 = raw8705step2 := by apply Matrix.ext; unfold raw8705step3 raw8705step2; decide +kernel
      have hl : raw8705step2Labels = labelEmbedding6 ∘ raw8705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8705step2 raw8705step2Labels raw8705step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw8706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8706 raw8706Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw8706 raw8706Labels = mixedMoment B raw8706step0 raw8706step0Labels := by
      have hz : ∀ j, raw8706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8706step0 = (fun i j => raw8706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8706step0 raw8706; decide +kernel
      have hl : raw8706step0Labels = raw8706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8706 raw8706Labels permutation346 hz
    mixedMoment B raw8706step0 raw8706step0Labels = mixedMoment B raw8706step1 raw8706step1Labels := by
      have ha : raw8706step1 = (fun i j => raw8706step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8706step1 raw8706step0; decide +kernel
      have hl : raw8706step1Labels = raw8706step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8706step0 raw8706step0Labels permutation151 permutation2
    mixedMoment B raw8706step1 raw8706step1Labels = mixedMoment B raw8706step2 raw8706step2Labels := by
      have ha : raw8706step2 = -raw8706step1 := by apply Matrix.ext; change ∀ i j, raw8706step2 i j = -(raw8706step1 i j); unfold raw8706step2 raw8706step1; decide +kernel
      have hl : raw8706step2Labels = raw8706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw8707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8707 raw8707Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw8707 raw8707Labels = mixedMoment B raw8707step0 raw8707step0Labels := by
      have hz : ∀ j, raw8707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8707step0 = (fun i j => raw8707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8707step0 raw8707; decide +kernel
      have hl : raw8707step0Labels = raw8707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8707 raw8707Labels permutation265 hz
    mixedMoment B raw8707step0 raw8707step0Labels = mixedMoment B raw8707step1 raw8707step1Labels := by
      have ha : raw8707step1 = (fun i j => raw8707step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8707step1 raw8707step0; decide +kernel
      have hl : raw8707step1Labels = raw8707step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8707step0 raw8707step0Labels permutation151 permutation2
    mixedMoment B raw8707step1 raw8707step1Labels = mixedMoment B raw8707step2 raw8707step2Labels := by
      have ha : raw8707step2 = -raw8707step1 := by apply Matrix.ext; change ∀ i j, raw8707step2 i j = -(raw8707step1 i j); unfold raw8707step2 raw8707step1; decide +kernel
      have hl : raw8707step2Labels = raw8707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw8708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8708step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw8708step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8708 raw8708Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw8708 raw8708Labels = mixedMoment B raw8708step0 raw8708step0Labels := by
      have hz : ∀ j, raw8708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8708step0 = (fun i j => raw8708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8708step0 raw8708; decide +kernel
      have hl : raw8708step0Labels = raw8708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8708 raw8708Labels permutation346 hz
    mixedMoment B raw8708step0 raw8708step0Labels = mixedMoment B raw8708step1 raw8708step1Labels := by
      have hz : ∀ j, raw8708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8708step1 = (fun i j => raw8708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8708step1 raw8708step0; decide +kernel
      have hl : raw8708step1Labels = raw8708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8708step0 raw8708step0Labels permutation56 hz
    mixedMoment B raw8708step1 raw8708step1Labels = mixedMoment B raw8708step2 raw8708step2Labels := by
      have ha : raw8708step2 = (fun i j => raw8708step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8708step2 raw8708step1; decide +kernel
      have hl : raw8708step2Labels = raw8708step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8708step1 raw8708step1Labels permutation31 permutation2
    mixedMoment B raw8708step2 raw8708step2Labels = mixedMoment B raw8708step3 raw8708step3Labels := by
      have ha : raw8708step3 = -raw8708step2 := by apply Matrix.ext; change ∀ i j, raw8708step3 i j = -(raw8708step2 i j); unfold raw8708step3 raw8708step2; decide +kernel
      have hl : raw8708step3Labels = raw8708step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw8709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw8709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8709step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8709 raw8709Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw8709 raw8709Labels = mixedMoment B raw8709step0 raw8709step0Labels := by
      have hz : ∀ j, raw8709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8709step0 = (fun i j => raw8709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8709step0 raw8709; decide +kernel
      have hl : raw8709step0Labels = raw8709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8709 raw8709Labels permutation346 hz
    mixedMoment B raw8709step0 raw8709step0Labels = mixedMoment B raw8709step1 raw8709step1Labels := by
      have hz : ∀ j, raw8709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8709step1 = (fun i j => raw8709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8709step1 raw8709step0; decide +kernel
      have hl : raw8709step1Labels = raw8709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8709step0 raw8709step0Labels permutation56 hz
    mixedMoment B raw8709step1 raw8709step1Labels = mixedMoment B raw8709step2 raw8709step2Labels := by
      have ha : raw8709step2 = (fun i j => raw8709step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8709step2 raw8709step1; decide +kernel
      have hl : raw8709step2Labels = raw8709step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8709step1 raw8709step1Labels permutation31 permutation2
    mixedMoment B raw8709step2 raw8709step2Labels = mixedMoment B raw8709step3 raw8709step3Labels := by
      have ha : raw8709step3 = -raw8709step2 := by apply Matrix.ext; change ∀ i j, raw8709step3 i j = -(raw8709step2 i j); unfold raw8709step3 raw8709step2; decide +kernel
      have hl : raw8709step3Labels = raw8709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw8710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw8710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8710 raw8710Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw8710 raw8710Labels = mixedMoment B raw8710step0 raw8710step0Labels := by
      have hz : ∀ j, raw8710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8710step0 = (fun i j => raw8710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8710step0 raw8710; decide +kernel
      have hl : raw8710step0Labels = raw8710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8710 raw8710Labels permutation346 hz
    mixedMoment B raw8710step0 raw8710step0Labels = mixedMoment B raw8710step1 raw8710step1Labels := by
      have ha : raw8710step1 = (fun i j => raw8710step0 (permutation80 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8710step1 raw8710step0; decide +kernel
      have hl : raw8710step1Labels = raw8710step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8710step0 raw8710step0Labels permutation80 permutation6
    mixedMoment B raw8710step1 raw8710step1Labels = mixedMoment B raw8710step2 raw8710step2Labels := by
      have ha : raw8710step2 = -raw8710step1 := by apply Matrix.ext; change ∀ i j, raw8710step2 i j = -(raw8710step1 i j); unfold raw8710step2 raw8710step1; decide +kernel
      have hl : raw8710step2Labels = raw8710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw8711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw8711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8711 raw8711Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw8711 raw8711Labels = mixedMoment B raw8711step0 raw8711step0Labels := by
      have hz : ∀ j, raw8711 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8711step0 = (fun i j => raw8711 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8711step0 raw8711; decide +kernel
      have hl : raw8711step0Labels = raw8711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8711 raw8711Labels permutation265 hz
    mixedMoment B raw8711step0 raw8711step0Labels = mixedMoment B raw8711step1 raw8711step1Labels := by
      have ha : raw8711step1 = (fun i j => raw8711step0 (permutation80 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8711step1 raw8711step0; decide +kernel
      have hl : raw8711step1Labels = raw8711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8711step0 raw8711step0Labels permutation80 permutation6
    mixedMoment B raw8711step1 raw8711step1Labels = mixedMoment B raw8711step2 raw8711step2Labels := by
      have ha : raw8711step2 = -raw8711step1 := by apply Matrix.ext; change ∀ i j, raw8711step2 i j = -(raw8711step1 i j); unfold raw8711step2 raw8711step1; decide +kernel
      have hl : raw8711step2Labels = raw8711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw8712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8712step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw8712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8712 raw8712Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw8712 raw8712Labels = mixedMoment B raw8712step0 raw8712step0Labels := by
      have hz : ∀ j, raw8712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8712step0 = (fun i j => raw8712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8712step0 raw8712; decide +kernel
      have hl : raw8712step0Labels = raw8712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8712 raw8712Labels permutation346 hz
    mixedMoment B raw8712step0 raw8712step0Labels = mixedMoment B raw8712step1 raw8712step1Labels := by
      have hz : ∀ j, raw8712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8712step1 = (fun i j => raw8712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8712step1 raw8712step0; decide +kernel
      have hl : raw8712step1Labels = raw8712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8712step0 raw8712step0Labels permutation56 hz
    mixedMoment B raw8712step1 raw8712step1Labels = mixedMoment B raw8712step2 raw8712step2Labels := by
      have ha : raw8712step2 = (fun i j => raw8712step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8712step2 raw8712step1; decide +kernel
      have hl : raw8712step2Labels = raw8712step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8712step1 raw8712step1Labels permutation8 permutation3
    _ = mixedMoment B node4006 node4006Labels := by rfl

def raw8713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8713step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8713 raw8713Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw8713 raw8713Labels = mixedMoment B raw8713step0 raw8713step0Labels := by
      have hz : ∀ j, raw8713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8713step0 = (fun i j => raw8713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8713step0 raw8713; decide +kernel
      have hl : raw8713step0Labels = raw8713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8713 raw8713Labels permutation346 hz
    mixedMoment B raw8713step0 raw8713step0Labels = mixedMoment B raw8713step1 raw8713step1Labels := by
      have hz : ∀ j, raw8713step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8713step1 = (fun i j => raw8713step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8713step1 raw8713step0; decide +kernel
      have hl : raw8713step1Labels = raw8713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8713step0 raw8713step0Labels permutation56 hz
    mixedMoment B raw8713step1 raw8713step1Labels = mixedMoment B raw8713step2 raw8713step2Labels := by
      have ha : raw8713step2 = (fun i j => raw8713step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8713step2 raw8713step1; decide +kernel
      have hl : raw8713step2Labels = raw8713step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8713step1 raw8713step1Labels permutation14 permutation6
    mixedMoment B raw8713step2 raw8713step2Labels = mixedMoment B raw8713step3 raw8713step3Labels := by
      have ha : raw8713step3 = -raw8713step2 := by apply Matrix.ext; change ∀ i j, raw8713step3 i j = -(raw8713step2 i j); unfold raw8713step3 raw8713step2; decide +kernel
      have hl : raw8713step3Labels = raw8713step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw8714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8714 raw8714Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw8714 raw8714Labels = mixedMoment B raw8714step0 raw8714step0Labels := by
      have hz : ∀ j, raw8714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8714step0 = (fun i j => raw8714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8714step0 raw8714; decide +kernel
      have hl : raw8714step0Labels = raw8714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8714 raw8714Labels permutation346 hz
    mixedMoment B raw8714step0 raw8714step0Labels = mixedMoment B raw8714step1 raw8714step1Labels := by
      have hz : ∀ j, raw8714step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8714step1 = (fun i j => raw8714step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8714step1 raw8714step0; decide +kernel
      have hl : raw8714step1Labels = raw8714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8714step0 raw8714step0Labels permutation56 hz
    mixedMoment B raw8714step1 raw8714step1Labels = mixedMoment B raw8714step2 raw8714step2Labels := by
      have ha : raw8714step2 = (fun i j => raw8714step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8714step2 raw8714step1; decide +kernel
      have hl : raw8714step2Labels = raw8714step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8714step1 raw8714step1Labels permutation14 permutation6
    mixedMoment B raw8714step2 raw8714step2Labels = mixedMoment B raw8714step3 raw8714step3Labels := by
      have ha : raw8714step3 = -raw8714step2 := by apply Matrix.ext; change ∀ i j, raw8714step3 i j = -(raw8714step2 i j); unfold raw8714step3 raw8714step2; decide +kernel
      have hl : raw8714step3Labels = raw8714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw8715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8715 raw8715Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw8715 raw8715Labels = mixedMoment B raw8715step0 raw8715step0Labels := by
      have hz : ∀ j, raw8715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8715step0 = (fun i j => raw8715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8715step0 raw8715; decide +kernel
      have hl : raw8715step0Labels = raw8715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8715 raw8715Labels permutation346 hz
    mixedMoment B raw8715step0 raw8715step0Labels = mixedMoment B raw8715step1 raw8715step1Labels := by
      have ha : raw8715step1 = (fun i j => raw8715step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8715step1 raw8715step0; decide +kernel
      have hl : raw8715step1Labels = raw8715step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8715step0 raw8715step0Labels permutation40 permutation3
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw8716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8716 raw8716Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw8716 raw8716Labels = mixedMoment B raw8716step0 raw8716step0Labels := by
      have ha : raw8716step0 = (fun i j => raw8716 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8716step0 raw8716; decide +kernel
      have hl : raw8716step0Labels = raw8716Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8716 raw8716Labels permutation184 permutation3
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw8717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8717 raw8717Labels = mixedMoment B node2638 node2638Labels := by
  calc
    mixedMoment B raw8717 raw8717Labels = mixedMoment B raw8717step0 raw8717step0Labels := by
      have hz : ∀ j, raw8717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8717step0 = (fun i j => raw8717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8717step0 raw8717; decide +kernel
      have hl : raw8717step0Labels = raw8717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8717 raw8717Labels permutation346 hz
    mixedMoment B raw8717step0 raw8717step0Labels = mixedMoment B raw8717step1 raw8717step1Labels := by
      have ha : raw8717step1 = (fun i j => raw8717step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8717step1 raw8717step0; decide +kernel
      have hl : raw8717step1Labels = raw8717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8717step0 raw8717step0Labels permutation40 permutation3
    _ = mixedMoment B node2638 node2638Labels := by rfl

def raw8718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8718 raw8718Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw8718 raw8718Labels = mixedMoment B raw8718step0 raw8718step0Labels := by
      have hz : ∀ j, raw8718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8718step0 = (fun i j => raw8718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8718step0 raw8718; decide +kernel
      have hl : raw8718step0Labels = raw8718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8718 raw8718Labels permutation346 hz
    mixedMoment B raw8718step0 raw8718step0Labels = mixedMoment B raw8718step1 raw8718step1Labels := by
      have ha : raw8718step1 = (fun i j => raw8718step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8718step1 raw8718step0; decide +kernel
      have hl : raw8718step1Labels = raw8718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8718step0 raw8718step0Labels permutation46 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw8719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8719 raw8719Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8719 raw8719Labels = mixedMoment B raw8719step0 raw8719step0Labels := by
      have hz : ∀ j, raw8719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8719step0 = (fun i j => raw8719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8719step0 raw8719; decide +kernel
      have hl : raw8719step0Labels = raw8719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8719 raw8719Labels permutation346 hz
    mixedMoment B raw8719step0 raw8719step0Labels = mixedMoment B raw8719step1 raw8719step1Labels := by
      have ha : raw8719step1 = (fun i j => raw8719step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8719step1 raw8719step0; decide +kernel
      have hl : raw8719step1Labels = raw8719step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8719step0 raw8719step0Labels permutation43 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8720 raw8720Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw8720 raw8720Labels = mixedMoment B raw8720step0 raw8720step0Labels := by
      have hz : ∀ j, raw8720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8720step0 = (fun i j => raw8720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8720step0 raw8720; decide +kernel
      have hl : raw8720step0Labels = raw8720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8720 raw8720Labels permutation265 hz
    mixedMoment B raw8720step0 raw8720step0Labels = mixedMoment B raw8720step1 raw8720step1Labels := by
      have ha : raw8720step1 = (fun i j => raw8720step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8720step1 raw8720step0; decide +kernel
      have hl : raw8720step1Labels = raw8720step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8720step0 raw8720step0Labels permutation40 permutation3
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw8721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8721 raw8721Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw8721 raw8721Labels = mixedMoment B raw8721step0 raw8721step0Labels := by
      have ha : raw8721step0 = (fun i j => raw8721 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8721step0 raw8721; decide +kernel
      have hl : raw8721step0Labels = raw8721Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8721 raw8721Labels permutation160 permutation3
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw8722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8722 raw8722Labels = mixedMoment B node2638 node2638Labels := by
  calc
    mixedMoment B raw8722 raw8722Labels = mixedMoment B raw8722step0 raw8722step0Labels := by
      have hz : ∀ j, raw8722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8722step0 = (fun i j => raw8722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8722step0 raw8722; decide +kernel
      have hl : raw8722step0Labels = raw8722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8722 raw8722Labels permutation265 hz
    mixedMoment B raw8722step0 raw8722step0Labels = mixedMoment B raw8722step1 raw8722step1Labels := by
      have ha : raw8722step1 = (fun i j => raw8722step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8722step1 raw8722step0; decide +kernel
      have hl : raw8722step1Labels = raw8722step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8722step0 raw8722step0Labels permutation40 permutation3
    _ = mixedMoment B node2638 node2638Labels := by rfl

def raw8723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8723 raw8723Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw8723 raw8723Labels = mixedMoment B raw8723step0 raw8723step0Labels := by
      have hz : ∀ j, raw8723 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8723step0 = (fun i j => raw8723 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8723step0 raw8723; decide +kernel
      have hl : raw8723step0Labels = raw8723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8723 raw8723Labels permutation265 hz
    mixedMoment B raw8723step0 raw8723step0Labels = mixedMoment B raw8723step1 raw8723step1Labels := by
      have ha : raw8723step1 = (fun i j => raw8723step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8723step1 raw8723step0; decide +kernel
      have hl : raw8723step1Labels = raw8723step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8723step0 raw8723step0Labels permutation46 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw8724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8724 raw8724Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8724 raw8724Labels = mixedMoment B raw8724step0 raw8724step0Labels := by
      have hz : ∀ j, raw8724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8724step0 = (fun i j => raw8724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8724step0 raw8724; decide +kernel
      have hl : raw8724step0Labels = raw8724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8724 raw8724Labels permutation265 hz
    mixedMoment B raw8724step0 raw8724step0Labels = mixedMoment B raw8724step1 raw8724step1Labels := by
      have ha : raw8724step1 = (fun i j => raw8724step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8724step1 raw8724step0; decide +kernel
      have hl : raw8724step1Labels = raw8724step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8724step0 raw8724step0Labels permutation43 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8725step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8725 raw8725Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw8725 raw8725Labels = mixedMoment B raw8725step0 raw8725step0Labels := by
      have hz : ∀ j, raw8725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8725step0 = (fun i j => raw8725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8725step0 raw8725; decide +kernel
      have hl : raw8725step0Labels = raw8725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8725 raw8725Labels permutation346 hz
    mixedMoment B raw8725step0 raw8725step0Labels = mixedMoment B raw8725step1 raw8725step1Labels := by
      have hz : ∀ j, raw8725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8725step1 = (fun i j => raw8725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8725step1 raw8725step0; decide +kernel
      have hl : raw8725step1Labels = raw8725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8725step0 raw8725step0Labels permutation56 hz
    mixedMoment B raw8725step1 raw8725step1Labels = mixedMoment B raw8725step2 raw8725step2Labels := by
      have ha : raw8725step2 = (fun i j => raw8725step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8725step2 raw8725step1; decide +kernel
      have hl : raw8725step2Labels = raw8725step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8725step1 raw8725step1Labels permutation10 permutation3
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw8726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8726 raw8726Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8726 raw8726Labels = mixedMoment B raw8726step0 raw8726step0Labels := by
      have hz : ∀ j, raw8726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8726step0 = (fun i j => raw8726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8726step0 raw8726; decide +kernel
      have hl : raw8726step0Labels = raw8726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8726 raw8726Labels permutation346 hz
    mixedMoment B raw8726step0 raw8726step0Labels = mixedMoment B raw8726step1 raw8726step1Labels := by
      have ha : raw8726step1 = (fun i j => raw8726step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8726step1 raw8726step0; decide +kernel
      have hl : raw8726step1Labels = raw8726step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8726step0 raw8726step0Labels permutation34 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw8727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8727 raw8727Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8727 raw8727Labels = mixedMoment B raw8727step0 raw8727step0Labels := by
      have hz : ∀ j, raw8727 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8727step0 = (fun i j => raw8727 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8727step0 raw8727; decide +kernel
      have hl : raw8727step0Labels = raw8727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8727 raw8727Labels permutation265 hz
    mixedMoment B raw8727step0 raw8727step0Labels = mixedMoment B raw8727step1 raw8727step1Labels := by
      have ha : raw8727step1 = (fun i j => raw8727step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8727step1 raw8727step0; decide +kernel
      have hl : raw8727step1Labels = raw8727step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8727step0 raw8727step0Labels permutation34 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw8728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8728step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8728 raw8728Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw8728 raw8728Labels = mixedMoment B raw8728step0 raw8728step0Labels := by
      have hz : ∀ j, raw8728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8728step0 = (fun i j => raw8728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8728step0 raw8728; decide +kernel
      have hl : raw8728step0Labels = raw8728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8728 raw8728Labels permutation346 hz
    mixedMoment B raw8728step0 raw8728step0Labels = mixedMoment B raw8728step1 raw8728step1Labels := by
      have hz : ∀ j, raw8728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8728step1 = (fun i j => raw8728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8728step1 raw8728step0; decide +kernel
      have hl : raw8728step1Labels = raw8728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8728step0 raw8728step0Labels permutation56 hz
    mixedMoment B raw8728step1 raw8728step1Labels = mixedMoment B raw8728step2 raw8728step2Labels := by
      have ha : raw8728step2 = (fun i j => raw8728step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8728step2 raw8728step1; decide +kernel
      have hl : raw8728step2Labels = raw8728step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8728step1 raw8728step1Labels permutation10 permutation3
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw8729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8729 raw8729Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw8729 raw8729Labels = mixedMoment B raw8729step0 raw8729step0Labels := by
      have hz : ∀ j, raw8729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8729step0 = (fun i j => raw8729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8729step0 raw8729; decide +kernel
      have hl : raw8729step0Labels = raw8729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8729 raw8729Labels permutation346 hz
    mixedMoment B raw8729step0 raw8729step0Labels = mixedMoment B raw8729step1 raw8729step1Labels := by
      have hz : ∀ j, raw8729step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8729step1 = (fun i j => raw8729step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8729step1 raw8729step0; decide +kernel
      have hl : raw8729step1Labels = raw8729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8729step0 raw8729step0Labels permutation56 hz
    mixedMoment B raw8729step1 raw8729step1Labels = mixedMoment B raw8729step2 raw8729step2Labels := by
      have ha : raw8729step2 = (fun i j => raw8729step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8729step2 raw8729step1; decide +kernel
      have hl : raw8729step2Labels = raw8729step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8729step1 raw8729step1Labels permutation13 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw8730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8730 raw8730Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw8730 raw8730Labels = mixedMoment B raw8730step0 raw8730step0Labels := by
      have hz : ∀ j, raw8730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8730step0 = (fun i j => raw8730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8730step0 raw8730; decide +kernel
      have hl : raw8730step0Labels = raw8730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8730 raw8730Labels permutation346 hz
    mixedMoment B raw8730step0 raw8730step0Labels = mixedMoment B raw8730step1 raw8730step1Labels := by
      have hz : ∀ j, raw8730step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8730step1 = (fun i j => raw8730step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8730step1 raw8730step0; decide +kernel
      have hl : raw8730step1Labels = raw8730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8730step0 raw8730step0Labels permutation56 hz
    mixedMoment B raw8730step1 raw8730step1Labels = mixedMoment B raw8730step2 raw8730step2Labels := by
      have ha : raw8730step2 = (fun i j => raw8730step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8730step2 raw8730step1; decide +kernel
      have hl : raw8730step2Labels = raw8730step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8730step1 raw8730step1Labels permutation9 permutation3
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw8731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8731 raw8731Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw8731 raw8731Labels = mixedMoment B raw8731step0 raw8731step0Labels := by
      have hz : ∀ j, raw8731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8731step0 = (fun i j => raw8731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8731step0 raw8731; decide +kernel
      have hl : raw8731step0Labels = raw8731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8731 raw8731Labels permutation346 hz
    mixedMoment B raw8731step0 raw8731step0Labels = mixedMoment B raw8731step1 raw8731step1Labels := by
      have ha : raw8731step1 = (fun i j => raw8731step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8731step1 raw8731step0; decide +kernel
      have hl : raw8731step1Labels = raw8731step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8731step0 raw8731step0Labels permutation33 permutation3
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw8732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8732 raw8732Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw8732 raw8732Labels = mixedMoment B raw8732step0 raw8732step0Labels := by
      have hz : ∀ j, raw8732 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8732step0 = (fun i j => raw8732 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8732step0 raw8732; decide +kernel
      have hl : raw8732step0Labels = raw8732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8732 raw8732Labels permutation265 hz
    mixedMoment B raw8732step0 raw8732step0Labels = mixedMoment B raw8732step1 raw8732step1Labels := by
      have ha : raw8732step1 = (fun i j => raw8732step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8732step1 raw8732step0; decide +kernel
      have hl : raw8732step1Labels = raw8732step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8732step0 raw8732step0Labels permutation33 permutation3
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw8733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8733step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw8733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8733 raw8733Labels = mixedMoment B node2644 node2644Labels := by
  calc
    mixedMoment B raw8733 raw8733Labels = mixedMoment B raw8733step0 raw8733step0Labels := by
      have hz : ∀ j, raw8733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8733step0 = (fun i j => raw8733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8733step0 raw8733; decide +kernel
      have hl : raw8733step0Labels = raw8733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8733 raw8733Labels permutation346 hz
    mixedMoment B raw8733step0 raw8733step0Labels = mixedMoment B raw8733step1 raw8733step1Labels := by
      have hz : ∀ j, raw8733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8733step1 = (fun i j => raw8733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8733step1 raw8733step0; decide +kernel
      have hl : raw8733step1Labels = raw8733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8733step0 raw8733step0Labels permutation56 hz
    mixedMoment B raw8733step1 raw8733step1Labels = mixedMoment B raw8733step2 raw8733step2Labels := by
      have ha : raw8733step2 = (fun i j => raw8733step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8733step2 raw8733step1; decide +kernel
      have hl : raw8733step2Labels = raw8733step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8733step1 raw8733step1Labels permutation9 permutation3
    _ = mixedMoment B node2644 node2644Labels := by rfl

def raw8734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8734step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8734 raw8734Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8734 raw8734Labels = mixedMoment B raw8734step0 raw8734step0Labels := by
      have hz : ∀ j, raw8734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8734step0 = (fun i j => raw8734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8734step0 raw8734; decide +kernel
      have hl : raw8734step0Labels = raw8734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8734 raw8734Labels permutation346 hz
    mixedMoment B raw8734step0 raw8734step0Labels = mixedMoment B raw8734step1 raw8734step1Labels := by
      have hz : ∀ j, raw8734step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8734step1 = (fun i j => raw8734step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8734step1 raw8734step0; decide +kernel
      have hl : raw8734step1Labels = raw8734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8734step0 raw8734step0Labels permutation56 hz
    mixedMoment B raw8734step1 raw8734step1Labels = mixedMoment B raw8734step2 raw8734step2Labels := by
      have ha : raw8734step2 = (fun i j => raw8734step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8734step2 raw8734step1; decide +kernel
      have hl : raw8734step2Labels = raw8734step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8734step1 raw8734step1Labels permutation9 permutation3
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw8735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8735 raw8735Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw8735 raw8735Labels = mixedMoment B raw8735step0 raw8735step0Labels := by
      have hz : ∀ j, raw8735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8735step0 = (fun i j => raw8735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8735step0 raw8735; decide +kernel
      have hl : raw8735step0Labels = raw8735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8735 raw8735Labels permutation346 hz
    mixedMoment B raw8735step0 raw8735step0Labels = mixedMoment B raw8735step1 raw8735step1Labels := by
      have hz : ∀ j, raw8735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8735step1 = (fun i j => raw8735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8735step1 raw8735step0; decide +kernel
      have hl : raw8735step1Labels = raw8735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8735step0 raw8735step0Labels permutation56 hz
    mixedMoment B raw8735step1 raw8735step1Labels = mixedMoment B raw8735step2 raw8735step2Labels := by
      have ha : raw8735step2 = (fun i j => raw8735step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8735step2 raw8735step1; decide +kernel
      have hl : raw8735step2Labels = raw8735step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8735step1 raw8735step1Labels permutation8 permutation3
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw8736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8736 raw8736Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw8736 raw8736Labels = mixedMoment B raw8736step0 raw8736step0Labels := by
      have hz : ∀ j, raw8736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8736step0 = (fun i j => raw8736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8736step0 raw8736; decide +kernel
      have hl : raw8736step0Labels = raw8736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8736 raw8736Labels permutation346 hz
    mixedMoment B raw8736step0 raw8736step0Labels = mixedMoment B raw8736step1 raw8736step1Labels := by
      have ha : raw8736step1 = (fun i j => raw8736step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8736step1 raw8736step0; decide +kernel
      have hl : raw8736step1Labels = raw8736step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8736step0 raw8736step0Labels permutation32 permutation3
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw8737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8737 raw8737Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw8737 raw8737Labels = mixedMoment B raw8737step0 raw8737step0Labels := by
      have hz : ∀ j, raw8737 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8737step0 = (fun i j => raw8737 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8737step0 raw8737; decide +kernel
      have hl : raw8737step0Labels = raw8737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8737 raw8737Labels permutation265 hz
    mixedMoment B raw8737step0 raw8737step0Labels = mixedMoment B raw8737step1 raw8737step1Labels := by
      have ha : raw8737step1 = (fun i j => raw8737step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8737step1 raw8737step0; decide +kernel
      have hl : raw8737step1Labels = raw8737step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8737step0 raw8737step0Labels permutation32 permutation3
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw8738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8738step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw8738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8738 raw8738Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw8738 raw8738Labels = mixedMoment B raw8738step0 raw8738step0Labels := by
      have hz : ∀ j, raw8738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8738step0 = (fun i j => raw8738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8738step0 raw8738; decide +kernel
      have hl : raw8738step0Labels = raw8738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8738 raw8738Labels permutation346 hz
    mixedMoment B raw8738step0 raw8738step0Labels = mixedMoment B raw8738step1 raw8738step1Labels := by
      have hz : ∀ j, raw8738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8738step1 = (fun i j => raw8738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8738step1 raw8738step0; decide +kernel
      have hl : raw8738step1Labels = raw8738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8738step0 raw8738step0Labels permutation56 hz
    mixedMoment B raw8738step1 raw8738step1Labels = mixedMoment B raw8738step2 raw8738step2Labels := by
      have ha : raw8738step2 = (fun i j => raw8738step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8738step2 raw8738step1; decide +kernel
      have hl : raw8738step2Labels = raw8738step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8738step1 raw8738step1Labels permutation8 permutation3
    _ = mixedMoment B node2640 node2640Labels := by rfl

def raw8739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8739step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw8739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8739 raw8739Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw8739 raw8739Labels = mixedMoment B raw8739step0 raw8739step0Labels := by
      have hz : ∀ j, raw8739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8739step0 = (fun i j => raw8739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8739step0 raw8739; decide +kernel
      have hl : raw8739step0Labels = raw8739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8739 raw8739Labels permutation346 hz
    mixedMoment B raw8739step0 raw8739step0Labels = mixedMoment B raw8739step1 raw8739step1Labels := by
      have hz : ∀ j, raw8739step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8739step1 = (fun i j => raw8739step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8739step1 raw8739step0; decide +kernel
      have hl : raw8739step1Labels = raw8739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8739step0 raw8739step0Labels permutation56 hz
    mixedMoment B raw8739step1 raw8739step1Labels = mixedMoment B raw8739step2 raw8739step2Labels := by
      have ha : raw8739step2 = (fun i j => raw8739step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8739step2 raw8739step1; decide +kernel
      have hl : raw8739step2Labels = raw8739step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8739step1 raw8739step1Labels permutation10 permutation3
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw8740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8740 raw8740Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw8740 raw8740Labels = mixedMoment B raw8740step0 raw8740step0Labels := by
      have hz : ∀ j, raw8740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8740step0 = (fun i j => raw8740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8740step0 raw8740; decide +kernel
      have hl : raw8740step0Labels = raw8740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8740 raw8740Labels permutation346 hz
    mixedMoment B raw8740step0 raw8740step0Labels = mixedMoment B raw8740step1 raw8740step1Labels := by
      have ha : raw8740step1 = (fun i j => raw8740step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8740step1 raw8740step0; decide +kernel
      have hl : raw8740step1Labels = raw8740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8740step0 raw8740step0Labels permutation148 permutation7
    mixedMoment B raw8740step1 raw8740step1Labels = mixedMoment B raw8740step2 raw8740step2Labels := by
      have ha : raw8740step2 = raw8740step1 := by apply Matrix.ext; unfold raw8740step2 raw8740step1; decide +kernel
      have hl : raw8740step1Labels = labelEmbedding1 ∘ raw8740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8740step1 raw8740step1Labels raw8740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw8741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8741 raw8741Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw8741 raw8741Labels = mixedMoment B raw8741step0 raw8741step0Labels := by
      have hz : ∀ j, raw8741 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8741step0 = (fun i j => raw8741 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8741step0 raw8741; decide +kernel
      have hl : raw8741step0Labels = raw8741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8741 raw8741Labels permutation265 hz
    mixedMoment B raw8741step0 raw8741step0Labels = mixedMoment B raw8741step1 raw8741step1Labels := by
      have ha : raw8741step1 = (fun i j => raw8741step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8741step1 raw8741step0; decide +kernel
      have hl : raw8741step1Labels = raw8741step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8741step0 raw8741step0Labels permutation148 permutation7
    mixedMoment B raw8741step1 raw8741step1Labels = mixedMoment B raw8741step2 raw8741step2Labels := by
      have ha : raw8741step2 = raw8741step1 := by apply Matrix.ext; unfold raw8741step2 raw8741step1; decide +kernel
      have hl : raw8741step1Labels = labelEmbedding1 ∘ raw8741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8741step1 raw8741step1Labels raw8741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw8742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8742step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8742step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8742step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8742 raw8742Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw8742 raw8742Labels = mixedMoment B raw8742step0 raw8742step0Labels := by
      have hz : ∀ j, raw8742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8742step0 = (fun i j => raw8742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8742step0 raw8742; decide +kernel
      have hl : raw8742step0Labels = raw8742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8742 raw8742Labels permutation346 hz
    mixedMoment B raw8742step0 raw8742step0Labels = mixedMoment B raw8742step1 raw8742step1Labels := by
      have hz : ∀ j, raw8742step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8742step1 = (fun i j => raw8742step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8742step1 raw8742step0; decide +kernel
      have hl : raw8742step1Labels = raw8742step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8742step0 raw8742step0Labels permutation56 hz
    mixedMoment B raw8742step1 raw8742step1Labels = mixedMoment B raw8742step2 raw8742step2Labels := by
      have ha : raw8742step2 = (fun i j => raw8742step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8742step2 raw8742step1; decide +kernel
      have hl : raw8742step2Labels = raw8742step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8742step1 raw8742step1Labels permutation30 permutation7
    mixedMoment B raw8742step2 raw8742step2Labels = mixedMoment B raw8742step3 raw8742step3Labels := by
      have ha : raw8742step3 = raw8742step2 := by apply Matrix.ext; unfold raw8742step3 raw8742step2; decide +kernel
      have hl : raw8742step2Labels = labelEmbedding1 ∘ raw8742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8742step2 raw8742step2Labels raw8742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw8743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8743step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8743step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8743step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw8743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8743 raw8743Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw8743 raw8743Labels = mixedMoment B raw8743step0 raw8743step0Labels := by
      have hz : ∀ j, raw8743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8743step0 = (fun i j => raw8743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8743step0 raw8743; decide +kernel
      have hl : raw8743step0Labels = raw8743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8743 raw8743Labels permutation346 hz
    mixedMoment B raw8743step0 raw8743step0Labels = mixedMoment B raw8743step1 raw8743step1Labels := by
      have hz : ∀ j, raw8743step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8743step1 = (fun i j => raw8743step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8743step1 raw8743step0; decide +kernel
      have hl : raw8743step1Labels = raw8743step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8743step0 raw8743step0Labels permutation56 hz
    mixedMoment B raw8743step1 raw8743step1Labels = mixedMoment B raw8743step2 raw8743step2Labels := by
      have ha : raw8743step2 = (fun i j => raw8743step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8743step2 raw8743step1; decide +kernel
      have hl : raw8743step2Labels = raw8743step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8743step1 raw8743step1Labels permutation30 permutation7
    mixedMoment B raw8743step2 raw8743step2Labels = mixedMoment B raw8743step3 raw8743step3Labels := by
      have ha : raw8743step3 = raw8743step2 := by apply Matrix.ext; unfold raw8743step3 raw8743step2; decide +kernel
      have hl : raw8743step2Labels = labelEmbedding1 ∘ raw8743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8743step2 raw8743step2Labels raw8743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw8744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8744step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8744step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8744 raw8744Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw8744 raw8744Labels = mixedMoment B raw8744step0 raw8744step0Labels := by
      have hz : ∀ j, raw8744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8744step0 = (fun i j => raw8744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8744step0 raw8744; decide +kernel
      have hl : raw8744step0Labels = raw8744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8744 raw8744Labels permutation346 hz
    mixedMoment B raw8744step0 raw8744step0Labels = mixedMoment B raw8744step1 raw8744step1Labels := by
      have hz : ∀ j, raw8744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8744step1 = (fun i j => raw8744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8744step1 raw8744step0; decide +kernel
      have hl : raw8744step1Labels = raw8744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8744step0 raw8744step0Labels permutation56 hz
    mixedMoment B raw8744step1 raw8744step1Labels = mixedMoment B raw8744step2 raw8744step2Labels := by
      have ha : raw8744step2 = (fun i j => raw8744step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8744step2 raw8744step1; decide +kernel
      have hl : raw8744step2Labels = raw8744step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8744step1 raw8744step1Labels permutation30 permutation7
    mixedMoment B raw8744step2 raw8744step2Labels = mixedMoment B raw8744step3 raw8744step3Labels := by
      have ha : raw8744step3 = raw8744step2 := by apply Matrix.ext; unfold raw8744step3 raw8744step2; decide +kernel
      have hl : raw8744step2Labels = labelEmbedding1 ∘ raw8744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8744step2 raw8744step2Labels raw8744step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw8745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8745 raw8745Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw8745 raw8745Labels = mixedMoment B raw8745step0 raw8745step0Labels := by
      have hz : ∀ j, raw8745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8745step0 = (fun i j => raw8745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8745step0 raw8745; decide +kernel
      have hl : raw8745step0Labels = raw8745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8745 raw8745Labels permutation346 hz
    mixedMoment B raw8745step0 raw8745step0Labels = mixedMoment B raw8745step1 raw8745step1Labels := by
      have ha : raw8745step1 = (fun i j => raw8745step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8745step1 raw8745step0; decide +kernel
      have hl : raw8745step1Labels = raw8745step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8745step0 raw8745step0Labels permutation48 permutation5
    mixedMoment B raw8745step1 raw8745step1Labels = mixedMoment B raw8745step2 raw8745step2Labels := by
      have ha : raw8745step2 = -raw8745step1 := by apply Matrix.ext; change ∀ i j, raw8745step2 i j = -(raw8745step1 i j); unfold raw8745step2 raw8745step1; decide +kernel
      have hl : raw8745step2Labels = raw8745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8745step2 raw8745step2Labels = mixedMoment B raw8745step3 raw8745step3Labels := by
      have ha : raw8745step3 = raw8745step2 := by apply Matrix.ext; unfold raw8745step3 raw8745step2; decide +kernel
      have hl : raw8745step2Labels = labelEmbedding1 ∘ raw8745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8745step2 raw8745step2Labels raw8745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw8746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8746 raw8746Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw8746 raw8746Labels = mixedMoment B raw8746step0 raw8746step0Labels := by
      have ha : raw8746step0 = (fun i j => raw8746 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8746step0 raw8746; decide +kernel
      have hl : raw8746step0Labels = raw8746Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8746 raw8746Labels permutation192 permutation5
    mixedMoment B raw8746step0 raw8746step0Labels = mixedMoment B raw8746step1 raw8746step1Labels := by
      have ha : raw8746step1 = -raw8746step0 := by apply Matrix.ext; change ∀ i j, raw8746step1 i j = -(raw8746step0 i j); unfold raw8746step1 raw8746step0; decide +kernel
      have hl : raw8746step1Labels = raw8746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8746step1 raw8746step1Labels = mixedMoment B raw8746step2 raw8746step2Labels := by
      have ha : raw8746step2 = raw8746step1 := by apply Matrix.ext; unfold raw8746step2 raw8746step1; decide +kernel
      have hl : raw8746step1Labels = labelEmbedding1 ∘ raw8746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8746step1 raw8746step1Labels raw8746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw8747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw8747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8747 raw8747Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw8747 raw8747Labels = mixedMoment B raw8747step0 raw8747step0Labels := by
      have hz : ∀ j, raw8747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8747step0 = (fun i j => raw8747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8747step0 raw8747; decide +kernel
      have hl : raw8747step0Labels = raw8747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8747 raw8747Labels permutation346 hz
    mixedMoment B raw8747step0 raw8747step0Labels = mixedMoment B raw8747step1 raw8747step1Labels := by
      have ha : raw8747step1 = (fun i j => raw8747step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8747step1 raw8747step0; decide +kernel
      have hl : raw8747step1Labels = raw8747step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8747step0 raw8747step0Labels permutation49 permutation5
    mixedMoment B raw8747step1 raw8747step1Labels = mixedMoment B raw8747step2 raw8747step2Labels := by
      have ha : raw8747step2 = -raw8747step1 := by apply Matrix.ext; change ∀ i j, raw8747step2 i j = -(raw8747step1 i j); unfold raw8747step2 raw8747step1; decide +kernel
      have hl : raw8747step2Labels = raw8747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8747step2 raw8747step2Labels = mixedMoment B raw8747step3 raw8747step3Labels := by
      have ha : raw8747step3 = raw8747step2 := by apply Matrix.ext; unfold raw8747step3 raw8747step2; decide +kernel
      have hl : raw8747step2Labels = labelEmbedding1 ∘ raw8747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8747step2 raw8747step2Labels raw8747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw8748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8748 raw8748Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw8748 raw8748Labels = mixedMoment B raw8748step0 raw8748step0Labels := by
      have hz : ∀ j, raw8748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8748step0 = (fun i j => raw8748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8748step0 raw8748; decide +kernel
      have hl : raw8748step0Labels = raw8748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8748 raw8748Labels permutation346 hz
    mixedMoment B raw8748step0 raw8748step0Labels = mixedMoment B raw8748step1 raw8748step1Labels := by
      have ha : raw8748step1 = (fun i j => raw8748step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8748step1 raw8748step0; decide +kernel
      have hl : raw8748step1Labels = raw8748step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8748step0 raw8748step0Labels permutation48 permutation5
    mixedMoment B raw8748step1 raw8748step1Labels = mixedMoment B raw8748step2 raw8748step2Labels := by
      have ha : raw8748step2 = -raw8748step1 := by apply Matrix.ext; change ∀ i j, raw8748step2 i j = -(raw8748step1 i j); unfold raw8748step2 raw8748step1; decide +kernel
      have hl : raw8748step2Labels = raw8748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8748step2 raw8748step2Labels = mixedMoment B raw8748step3 raw8748step3Labels := by
      have ha : raw8748step3 = raw8748step2 := by apply Matrix.ext; unfold raw8748step3 raw8748step2; decide +kernel
      have hl : raw8748step2Labels = labelEmbedding1 ∘ raw8748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8748step2 raw8748step2Labels raw8748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw8749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8749step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8749step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8749 raw8749Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8749 raw8749Labels = mixedMoment B raw8749step0 raw8749step0Labels := by
      have hz : ∀ j, raw8749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8749step0 = (fun i j => raw8749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8749step0 raw8749; decide +kernel
      have hl : raw8749step0Labels = raw8749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8749 raw8749Labels permutation346 hz
    mixedMoment B raw8749step0 raw8749step0Labels = mixedMoment B raw8749step1 raw8749step1Labels := by
      have ha : raw8749step1 = (fun i j => raw8749step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8749step1 raw8749step0; decide +kernel
      have hl : raw8749step1Labels = raw8749step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8749step0 raw8749step0Labels permutation54 permutation5
    mixedMoment B raw8749step1 raw8749step1Labels = mixedMoment B raw8749step2 raw8749step2Labels := by
      have ha : raw8749step2 = -raw8749step1 := by apply Matrix.ext; change ∀ i j, raw8749step2 i j = -(raw8749step1 i j); unfold raw8749step2 raw8749step1; decide +kernel
      have hl : raw8749step2Labels = raw8749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8749step2 raw8749step2Labels = mixedMoment B raw8749step3 raw8749step3Labels := by
      have ha : raw8749step3 = raw8749step2 := by apply Matrix.ext; unfold raw8749step3 raw8749step2; decide +kernel
      have hl : raw8749step2Labels = labelEmbedding1 ∘ raw8749step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8749step2 raw8749step2Labels raw8749step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8750 raw8750Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw8750 raw8750Labels = mixedMoment B raw8750step0 raw8750step0Labels := by
      have hz : ∀ j, raw8750 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8750step0 = (fun i j => raw8750 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8750step0 raw8750; decide +kernel
      have hl : raw8750step0Labels = raw8750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8750 raw8750Labels permutation265 hz
    mixedMoment B raw8750step0 raw8750step0Labels = mixedMoment B raw8750step1 raw8750step1Labels := by
      have ha : raw8750step1 = (fun i j => raw8750step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8750step1 raw8750step0; decide +kernel
      have hl : raw8750step1Labels = raw8750step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8750step0 raw8750step0Labels permutation48 permutation5
    mixedMoment B raw8750step1 raw8750step1Labels = mixedMoment B raw8750step2 raw8750step2Labels := by
      have ha : raw8750step2 = -raw8750step1 := by apply Matrix.ext; change ∀ i j, raw8750step2 i j = -(raw8750step1 i j); unfold raw8750step2 raw8750step1; decide +kernel
      have hl : raw8750step2Labels = raw8750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8750step2 raw8750step2Labels = mixedMoment B raw8750step3 raw8750step3Labels := by
      have ha : raw8750step3 = raw8750step2 := by apply Matrix.ext; unfold raw8750step3 raw8750step2; decide +kernel
      have hl : raw8750step2Labels = labelEmbedding1 ∘ raw8750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8750step2 raw8750step2Labels raw8750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw8751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8751 raw8751Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw8751 raw8751Labels = mixedMoment B raw8751step0 raw8751step0Labels := by
      have ha : raw8751step0 = (fun i j => raw8751 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8751step0 raw8751; decide +kernel
      have hl : raw8751step0Labels = raw8751Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8751 raw8751Labels permutation168 permutation5
    mixedMoment B raw8751step0 raw8751step0Labels = mixedMoment B raw8751step1 raw8751step1Labels := by
      have ha : raw8751step1 = -raw8751step0 := by apply Matrix.ext; change ∀ i j, raw8751step1 i j = -(raw8751step0 i j); unfold raw8751step1 raw8751step0; decide +kernel
      have hl : raw8751step1Labels = raw8751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8751step1 raw8751step1Labels = mixedMoment B raw8751step2 raw8751step2Labels := by
      have ha : raw8751step2 = raw8751step1 := by apply Matrix.ext; unfold raw8751step2 raw8751step1; decide +kernel
      have hl : raw8751step1Labels = labelEmbedding1 ∘ raw8751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8751step1 raw8751step1Labels raw8751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw8752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw8752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw8752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8752 raw8752Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw8752 raw8752Labels = mixedMoment B raw8752step0 raw8752step0Labels := by
      have hz : ∀ j, raw8752 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8752step0 = (fun i j => raw8752 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8752step0 raw8752; decide +kernel
      have hl : raw8752step0Labels = raw8752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8752 raw8752Labels permutation265 hz
    mixedMoment B raw8752step0 raw8752step0Labels = mixedMoment B raw8752step1 raw8752step1Labels := by
      have ha : raw8752step1 = (fun i j => raw8752step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8752step1 raw8752step0; decide +kernel
      have hl : raw8752step1Labels = raw8752step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8752step0 raw8752step0Labels permutation49 permutation5
    mixedMoment B raw8752step1 raw8752step1Labels = mixedMoment B raw8752step2 raw8752step2Labels := by
      have ha : raw8752step2 = -raw8752step1 := by apply Matrix.ext; change ∀ i j, raw8752step2 i j = -(raw8752step1 i j); unfold raw8752step2 raw8752step1; decide +kernel
      have hl : raw8752step2Labels = raw8752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8752step2 raw8752step2Labels = mixedMoment B raw8752step3 raw8752step3Labels := by
      have ha : raw8752step3 = raw8752step2 := by apply Matrix.ext; unfold raw8752step3 raw8752step2; decide +kernel
      have hl : raw8752step2Labels = labelEmbedding1 ∘ raw8752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8752step2 raw8752step2Labels raw8752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw8753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw8753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw8753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8753 raw8753Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw8753 raw8753Labels = mixedMoment B raw8753step0 raw8753step0Labels := by
      have hz : ∀ j, raw8753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8753step0 = (fun i j => raw8753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8753step0 raw8753; decide +kernel
      have hl : raw8753step0Labels = raw8753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8753 raw8753Labels permutation265 hz
    mixedMoment B raw8753step0 raw8753step0Labels = mixedMoment B raw8753step1 raw8753step1Labels := by
      have ha : raw8753step1 = (fun i j => raw8753step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8753step1 raw8753step0; decide +kernel
      have hl : raw8753step1Labels = raw8753step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8753step0 raw8753step0Labels permutation48 permutation5
    mixedMoment B raw8753step1 raw8753step1Labels = mixedMoment B raw8753step2 raw8753step2Labels := by
      have ha : raw8753step2 = -raw8753step1 := by apply Matrix.ext; change ∀ i j, raw8753step2 i j = -(raw8753step1 i j); unfold raw8753step2 raw8753step1; decide +kernel
      have hl : raw8753step2Labels = raw8753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8753step2 raw8753step2Labels = mixedMoment B raw8753step3 raw8753step3Labels := by
      have ha : raw8753step3 = raw8753step2 := by apply Matrix.ext; unfold raw8753step3 raw8753step2; decide +kernel
      have hl : raw8753step2Labels = labelEmbedding1 ∘ raw8753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8753step2 raw8753step2Labels raw8753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw8754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8754 raw8754Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8754 raw8754Labels = mixedMoment B raw8754step0 raw8754step0Labels := by
      have hz : ∀ j, raw8754 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8754step0 = (fun i j => raw8754 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8754step0 raw8754; decide +kernel
      have hl : raw8754step0Labels = raw8754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8754 raw8754Labels permutation265 hz
    mixedMoment B raw8754step0 raw8754step0Labels = mixedMoment B raw8754step1 raw8754step1Labels := by
      have ha : raw8754step1 = (fun i j => raw8754step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8754step1 raw8754step0; decide +kernel
      have hl : raw8754step1Labels = raw8754step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8754step0 raw8754step0Labels permutation54 permutation5
    mixedMoment B raw8754step1 raw8754step1Labels = mixedMoment B raw8754step2 raw8754step2Labels := by
      have ha : raw8754step2 = -raw8754step1 := by apply Matrix.ext; change ∀ i j, raw8754step2 i j = -(raw8754step1 i j); unfold raw8754step2 raw8754step1; decide +kernel
      have hl : raw8754step2Labels = raw8754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8754step2 raw8754step2Labels = mixedMoment B raw8754step3 raw8754step3Labels := by
      have ha : raw8754step3 = raw8754step2 := by apply Matrix.ext; unfold raw8754step3 raw8754step2; decide +kernel
      have hl : raw8754step2Labels = labelEmbedding1 ∘ raw8754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8754step2 raw8754step2Labels raw8754step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8755step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw8755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8755step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8755step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8755step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8755 raw8755Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw8755 raw8755Labels = mixedMoment B raw8755step0 raw8755step0Labels := by
      have hz : ∀ j, raw8755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8755step0 = (fun i j => raw8755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8755step0 raw8755; decide +kernel
      have hl : raw8755step0Labels = raw8755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8755 raw8755Labels permutation346 hz
    mixedMoment B raw8755step0 raw8755step0Labels = mixedMoment B raw8755step1 raw8755step1Labels := by
      have hz : ∀ j, raw8755step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8755step1 = (fun i j => raw8755step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8755step1 raw8755step0; decide +kernel
      have hl : raw8755step1Labels = raw8755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8755step0 raw8755step0Labels permutation56 hz
    mixedMoment B raw8755step1 raw8755step1Labels = mixedMoment B raw8755step2 raw8755step2Labels := by
      have ha : raw8755step2 = (fun i j => raw8755step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8755step2 raw8755step1; decide +kernel
      have hl : raw8755step2Labels = raw8755step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8755step1 raw8755step1Labels permutation11 permutation5
    mixedMoment B raw8755step2 raw8755step2Labels = mixedMoment B raw8755step3 raw8755step3Labels := by
      have ha : raw8755step3 = -raw8755step2 := by apply Matrix.ext; change ∀ i j, raw8755step3 i j = -(raw8755step2 i j); unfold raw8755step3 raw8755step2; decide +kernel
      have hl : raw8755step3Labels = raw8755step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8755step3 raw8755step3Labels = mixedMoment B raw8755step4 raw8755step4Labels := by
      have ha : raw8755step4 = raw8755step3 := by apply Matrix.ext; unfold raw8755step4 raw8755step3; decide +kernel
      have hl : raw8755step3Labels = labelEmbedding1 ∘ raw8755step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8755step3 raw8755step3Labels raw8755step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw8756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8756 raw8756Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8756 raw8756Labels = mixedMoment B raw8756step0 raw8756step0Labels := by
      have hz : ∀ j, raw8756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8756step0 = (fun i j => raw8756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8756step0 raw8756; decide +kernel
      have hl : raw8756step0Labels = raw8756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8756 raw8756Labels permutation346 hz
    mixedMoment B raw8756step0 raw8756step0Labels = mixedMoment B raw8756step1 raw8756step1Labels := by
      have ha : raw8756step1 = (fun i j => raw8756step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8756step1 raw8756step0; decide +kernel
      have hl : raw8756step1Labels = raw8756step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8756step0 raw8756step0Labels permutation103 permutation5
    mixedMoment B raw8756step1 raw8756step1Labels = mixedMoment B raw8756step2 raw8756step2Labels := by
      have ha : raw8756step2 = raw8756step1 := by apply Matrix.ext; unfold raw8756step2 raw8756step1; decide +kernel
      have hl : raw8756step1Labels = labelEmbedding1 ∘ raw8756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8756step1 raw8756step1Labels raw8756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8757 raw8757Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8757 raw8757Labels = mixedMoment B raw8757step0 raw8757step0Labels := by
      have hz : ∀ j, raw8757 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8757step0 = (fun i j => raw8757 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8757step0 raw8757; decide +kernel
      have hl : raw8757step0Labels = raw8757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8757 raw8757Labels permutation265 hz
    mixedMoment B raw8757step0 raw8757step0Labels = mixedMoment B raw8757step1 raw8757step1Labels := by
      have ha : raw8757step1 = (fun i j => raw8757step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8757step1 raw8757step0; decide +kernel
      have hl : raw8757step1Labels = raw8757step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8757step0 raw8757step0Labels permutation103 permutation5
    mixedMoment B raw8757step1 raw8757step1Labels = mixedMoment B raw8757step2 raw8757step2Labels := by
      have ha : raw8757step2 = raw8757step1 := by apply Matrix.ext; unfold raw8757step2 raw8757step1; decide +kernel
      have hl : raw8757step1Labels = labelEmbedding1 ∘ raw8757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8757step1 raw8757step1Labels raw8757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8758step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8758 raw8758Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw8758 raw8758Labels = mixedMoment B raw8758step0 raw8758step0Labels := by
      have hz : ∀ j, raw8758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8758step0 = (fun i j => raw8758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8758step0 raw8758; decide +kernel
      have hl : raw8758step0Labels = raw8758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8758 raw8758Labels permutation346 hz
    mixedMoment B raw8758step0 raw8758step0Labels = mixedMoment B raw8758step1 raw8758step1Labels := by
      have hz : ∀ j, raw8758step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8758step1 = (fun i j => raw8758step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8758step1 raw8758step0; decide +kernel
      have hl : raw8758step1Labels = raw8758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8758step0 raw8758step0Labels permutation56 hz
    mixedMoment B raw8758step1 raw8758step1Labels = mixedMoment B raw8758step2 raw8758step2Labels := by
      have ha : raw8758step2 = (fun i j => raw8758step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8758step2 raw8758step1; decide +kernel
      have hl : raw8758step2Labels = raw8758step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8758step1 raw8758step1Labels permutation19 permutation5
    mixedMoment B raw8758step2 raw8758step2Labels = mixedMoment B raw8758step3 raw8758step3Labels := by
      have ha : raw8758step3 = raw8758step2 := by apply Matrix.ext; unfold raw8758step3 raw8758step2; decide +kernel
      have hl : raw8758step2Labels = labelEmbedding1 ∘ raw8758step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8758step2 raw8758step2Labels raw8758step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw8759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8759step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8759step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8759 raw8759Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw8759 raw8759Labels = mixedMoment B raw8759step0 raw8759step0Labels := by
      have hz : ∀ j, raw8759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8759step0 = (fun i j => raw8759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8759step0 raw8759; decide +kernel
      have hl : raw8759step0Labels = raw8759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8759 raw8759Labels permutation346 hz
    mixedMoment B raw8759step0 raw8759step0Labels = mixedMoment B raw8759step1 raw8759step1Labels := by
      have hz : ∀ j, raw8759step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8759step1 = (fun i j => raw8759step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8759step1 raw8759step0; decide +kernel
      have hl : raw8759step1Labels = raw8759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8759step0 raw8759step0Labels permutation56 hz
    mixedMoment B raw8759step1 raw8759step1Labels = mixedMoment B raw8759step2 raw8759step2Labels := by
      have ha : raw8759step2 = (fun i j => raw8759step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8759step2 raw8759step1; decide +kernel
      have hl : raw8759step2Labels = raw8759step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8759step1 raw8759step1Labels permutation17 permutation5
    mixedMoment B raw8759step2 raw8759step2Labels = mixedMoment B raw8759step3 raw8759step3Labels := by
      have ha : raw8759step3 = raw8759step2 := by apply Matrix.ext; unfold raw8759step3 raw8759step2; decide +kernel
      have hl : raw8759step2Labels = labelEmbedding1 ∘ raw8759step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8759step2 raw8759step2Labels raw8759step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw8760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8760step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8760step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8760step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8760step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8760step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8760step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8760 raw8760Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw8760 raw8760Labels = mixedMoment B raw8760step0 raw8760step0Labels := by
      have hz : ∀ j, raw8760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8760step0 = (fun i j => raw8760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8760step0 raw8760; decide +kernel
      have hl : raw8760step0Labels = raw8760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8760 raw8760Labels permutation346 hz
    mixedMoment B raw8760step0 raw8760step0Labels = mixedMoment B raw8760step1 raw8760step1Labels := by
      have hz : ∀ j, raw8760step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8760step1 = (fun i j => raw8760step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8760step1 raw8760step0; decide +kernel
      have hl : raw8760step1Labels = raw8760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8760step0 raw8760step0Labels permutation56 hz
    mixedMoment B raw8760step1 raw8760step1Labels = mixedMoment B raw8760step2 raw8760step2Labels := by
      have ha : raw8760step2 = (fun i j => raw8760step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8760step2 raw8760step1; decide +kernel
      have hl : raw8760step2Labels = raw8760step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8760step1 raw8760step1Labels permutation13 permutation5
    mixedMoment B raw8760step2 raw8760step2Labels = mixedMoment B raw8760step3 raw8760step3Labels := by
      have ha : raw8760step3 = -raw8760step2 := by apply Matrix.ext; change ∀ i j, raw8760step3 i j = -(raw8760step2 i j); unfold raw8760step3 raw8760step2; decide +kernel
      have hl : raw8760step3Labels = raw8760step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8760step3 raw8760step3Labels = mixedMoment B raw8760step4 raw8760step4Labels := by
      have ha : raw8760step4 = raw8760step3 := by apply Matrix.ext; unfold raw8760step4 raw8760step3; decide +kernel
      have hl : raw8760step3Labels = labelEmbedding1 ∘ raw8760step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8760step3 raw8760step3Labels raw8760step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw8761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8761step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8761 raw8761Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw8761 raw8761Labels = mixedMoment B raw8761step0 raw8761step0Labels := by
      have hz : ∀ j, raw8761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8761step0 = (fun i j => raw8761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8761step0 raw8761; decide +kernel
      have hl : raw8761step0Labels = raw8761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8761 raw8761Labels permutation346 hz
    mixedMoment B raw8761step0 raw8761step0Labels = mixedMoment B raw8761step1 raw8761step1Labels := by
      have ha : raw8761step1 = (fun i j => raw8761step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8761step1 raw8761step0; decide +kernel
      have hl : raw8761step1Labels = raw8761step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8761step0 raw8761step0Labels permutation37 permutation5
    mixedMoment B raw8761step1 raw8761step1Labels = mixedMoment B raw8761step2 raw8761step2Labels := by
      have ha : raw8761step2 = -raw8761step1 := by apply Matrix.ext; change ∀ i j, raw8761step2 i j = -(raw8761step1 i j); unfold raw8761step2 raw8761step1; decide +kernel
      have hl : raw8761step2Labels = raw8761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8761step2 raw8761step2Labels = mixedMoment B raw8761step3 raw8761step3Labels := by
      have ha : raw8761step3 = raw8761step2 := by apply Matrix.ext; unfold raw8761step3 raw8761step2; decide +kernel
      have hl : raw8761step2Labels = labelEmbedding1 ∘ raw8761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8761step2 raw8761step2Labels raw8761step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw8762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw8762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8762step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw8762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8762 raw8762Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw8762 raw8762Labels = mixedMoment B raw8762step0 raw8762step0Labels := by
      have hz : ∀ j, raw8762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8762step0 = (fun i j => raw8762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8762step0 raw8762; decide +kernel
      have hl : raw8762step0Labels = raw8762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8762 raw8762Labels permutation265 hz
    mixedMoment B raw8762step0 raw8762step0Labels = mixedMoment B raw8762step1 raw8762step1Labels := by
      have ha : raw8762step1 = (fun i j => raw8762step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8762step1 raw8762step0; decide +kernel
      have hl : raw8762step1Labels = raw8762step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8762step0 raw8762step0Labels permutation37 permutation5
    mixedMoment B raw8762step1 raw8762step1Labels = mixedMoment B raw8762step2 raw8762step2Labels := by
      have ha : raw8762step2 = -raw8762step1 := by apply Matrix.ext; change ∀ i j, raw8762step2 i j = -(raw8762step1 i j); unfold raw8762step2 raw8762step1; decide +kernel
      have hl : raw8762step2Labels = raw8762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8762step2 raw8762step2Labels = mixedMoment B raw8762step3 raw8762step3Labels := by
      have ha : raw8762step3 = raw8762step2 := by apply Matrix.ext; unfold raw8762step3 raw8762step2; decide +kernel
      have hl : raw8762step2Labels = labelEmbedding1 ∘ raw8762step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8762step2 raw8762step2Labels raw8762step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw8763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8763step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8763step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw8763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8763step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8763step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8763step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw8763step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8763 raw8763Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw8763 raw8763Labels = mixedMoment B raw8763step0 raw8763step0Labels := by
      have hz : ∀ j, raw8763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8763step0 = (fun i j => raw8763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8763step0 raw8763; decide +kernel
      have hl : raw8763step0Labels = raw8763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8763 raw8763Labels permutation346 hz
    mixedMoment B raw8763step0 raw8763step0Labels = mixedMoment B raw8763step1 raw8763step1Labels := by
      have hz : ∀ j, raw8763step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8763step1 = (fun i j => raw8763step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8763step1 raw8763step0; decide +kernel
      have hl : raw8763step1Labels = raw8763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8763step0 raw8763step0Labels permutation56 hz
    mixedMoment B raw8763step1 raw8763step1Labels = mixedMoment B raw8763step2 raw8763step2Labels := by
      have ha : raw8763step2 = (fun i j => raw8763step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8763step2 raw8763step1; decide +kernel
      have hl : raw8763step2Labels = raw8763step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8763step1 raw8763step1Labels permutation12 permutation5
    mixedMoment B raw8763step2 raw8763step2Labels = mixedMoment B raw8763step3 raw8763step3Labels := by
      have ha : raw8763step3 = -raw8763step2 := by apply Matrix.ext; change ∀ i j, raw8763step3 i j = -(raw8763step2 i j); unfold raw8763step3 raw8763step2; decide +kernel
      have hl : raw8763step3Labels = raw8763step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8763step3 raw8763step3Labels = mixedMoment B raw8763step4 raw8763step4Labels := by
      have ha : raw8763step4 = raw8763step3 := by apply Matrix.ext; unfold raw8763step4 raw8763step3; decide +kernel
      have hl : raw8763step3Labels = labelEmbedding1 ∘ raw8763step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8763step3 raw8763step3Labels raw8763step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw8764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw8764step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8764step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8764step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8764step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8764 raw8764Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw8764 raw8764Labels = mixedMoment B raw8764step0 raw8764step0Labels := by
      have hz : ∀ j, raw8764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8764step0 = (fun i j => raw8764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8764step0 raw8764; decide +kernel
      have hl : raw8764step0Labels = raw8764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8764 raw8764Labels permutation346 hz
    mixedMoment B raw8764step0 raw8764step0Labels = mixedMoment B raw8764step1 raw8764step1Labels := by
      have hz : ∀ j, raw8764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8764step1 = (fun i j => raw8764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8764step1 raw8764step0; decide +kernel
      have hl : raw8764step1Labels = raw8764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8764step0 raw8764step0Labels permutation56 hz
    mixedMoment B raw8764step1 raw8764step1Labels = mixedMoment B raw8764step2 raw8764step2Labels := by
      have ha : raw8764step2 = (fun i j => raw8764step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8764step2 raw8764step1; decide +kernel
      have hl : raw8764step2Labels = raw8764step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8764step1 raw8764step1Labels permutation13 permutation5
    mixedMoment B raw8764step2 raw8764step2Labels = mixedMoment B raw8764step3 raw8764step3Labels := by
      have ha : raw8764step3 = -raw8764step2 := by apply Matrix.ext; change ∀ i j, raw8764step3 i j = -(raw8764step2 i j); unfold raw8764step3 raw8764step2; decide +kernel
      have hl : raw8764step3Labels = raw8764step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8764step3 raw8764step3Labels = mixedMoment B raw8764step4 raw8764step4Labels := by
      have ha : raw8764step4 = raw8764step3 := by apply Matrix.ext; unfold raw8764step4 raw8764step3; decide +kernel
      have hl : raw8764step3Labels = labelEmbedding1 ∘ raw8764step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8764step3 raw8764step3Labels raw8764step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw8765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8765step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8765step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8765step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8765step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8765step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8765 raw8765Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw8765 raw8765Labels = mixedMoment B raw8765step0 raw8765step0Labels := by
      have hz : ∀ j, raw8765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8765step0 = (fun i j => raw8765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8765step0 raw8765; decide +kernel
      have hl : raw8765step0Labels = raw8765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8765 raw8765Labels permutation346 hz
    mixedMoment B raw8765step0 raw8765step0Labels = mixedMoment B raw8765step1 raw8765step1Labels := by
      have hz : ∀ j, raw8765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8765step1 = (fun i j => raw8765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8765step1 raw8765step0; decide +kernel
      have hl : raw8765step1Labels = raw8765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8765step0 raw8765step0Labels permutation56 hz
    mixedMoment B raw8765step1 raw8765step1Labels = mixedMoment B raw8765step2 raw8765step2Labels := by
      have ha : raw8765step2 = (fun i j => raw8765step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8765step2 raw8765step1; decide +kernel
      have hl : raw8765step2Labels = raw8765step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8765step1 raw8765step1Labels permutation11 permutation5
    mixedMoment B raw8765step2 raw8765step2Labels = mixedMoment B raw8765step3 raw8765step3Labels := by
      have ha : raw8765step3 = -raw8765step2 := by apply Matrix.ext; change ∀ i j, raw8765step3 i j = -(raw8765step2 i j); unfold raw8765step3 raw8765step2; decide +kernel
      have hl : raw8765step3Labels = raw8765step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8765step3 raw8765step3Labels = mixedMoment B raw8765step4 raw8765step4Labels := by
      have ha : raw8765step4 = raw8765step3 := by apply Matrix.ext; unfold raw8765step4 raw8765step3; decide +kernel
      have hl : raw8765step3Labels = labelEmbedding1 ∘ raw8765step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8765step3 raw8765step3Labels raw8765step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw8766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8766step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8766step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8766 raw8766Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw8766 raw8766Labels = mixedMoment B raw8766step0 raw8766step0Labels := by
      have hz : ∀ j, raw8766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8766step0 = (fun i j => raw8766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8766step0 raw8766; decide +kernel
      have hl : raw8766step0Labels = raw8766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8766 raw8766Labels permutation346 hz
    mixedMoment B raw8766step0 raw8766step0Labels = mixedMoment B raw8766step1 raw8766step1Labels := by
      have ha : raw8766step1 = (fun i j => raw8766step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8766step1 raw8766step0; decide +kernel
      have hl : raw8766step1Labels = raw8766step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8766step0 raw8766step0Labels permutation35 permutation5
    mixedMoment B raw8766step1 raw8766step1Labels = mixedMoment B raw8766step2 raw8766step2Labels := by
      have ha : raw8766step2 = -raw8766step1 := by apply Matrix.ext; change ∀ i j, raw8766step2 i j = -(raw8766step1 i j); unfold raw8766step2 raw8766step1; decide +kernel
      have hl : raw8766step2Labels = raw8766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8766step2 raw8766step2Labels = mixedMoment B raw8766step3 raw8766step3Labels := by
      have ha : raw8766step3 = raw8766step2 := by apply Matrix.ext; unfold raw8766step3 raw8766step2; decide +kernel
      have hl : raw8766step2Labels = labelEmbedding1 ∘ raw8766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8766step2 raw8766step2Labels raw8766step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw8767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8767step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw8767step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8767step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw8767step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8767 raw8767Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw8767 raw8767Labels = mixedMoment B raw8767step0 raw8767step0Labels := by
      have hz : ∀ j, raw8767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8767step0 = (fun i j => raw8767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8767step0 raw8767; decide +kernel
      have hl : raw8767step0Labels = raw8767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8767 raw8767Labels permutation265 hz
    mixedMoment B raw8767step0 raw8767step0Labels = mixedMoment B raw8767step1 raw8767step1Labels := by
      have ha : raw8767step1 = (fun i j => raw8767step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8767step1 raw8767step0; decide +kernel
      have hl : raw8767step1Labels = raw8767step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8767step0 raw8767step0Labels permutation35 permutation5
    mixedMoment B raw8767step1 raw8767step1Labels = mixedMoment B raw8767step2 raw8767step2Labels := by
      have ha : raw8767step2 = -raw8767step1 := by apply Matrix.ext; change ∀ i j, raw8767step2 i j = -(raw8767step1 i j); unfold raw8767step2 raw8767step1; decide +kernel
      have hl : raw8767step2Labels = raw8767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8767step2 raw8767step2Labels = mixedMoment B raw8767step3 raw8767step3Labels := by
      have ha : raw8767step3 = raw8767step2 := by apply Matrix.ext; unfold raw8767step3 raw8767step2; decide +kernel
      have hl : raw8767step2Labels = labelEmbedding1 ∘ raw8767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8767step2 raw8767step2Labels raw8767step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw8768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8768step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8768step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8768step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8768 raw8768Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw8768 raw8768Labels = mixedMoment B raw8768step0 raw8768step0Labels := by
      have hz : ∀ j, raw8768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8768step0 = (fun i j => raw8768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8768step0 raw8768; decide +kernel
      have hl : raw8768step0Labels = raw8768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8768 raw8768Labels permutation346 hz
    mixedMoment B raw8768step0 raw8768step0Labels = mixedMoment B raw8768step1 raw8768step1Labels := by
      have hz : ∀ j, raw8768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8768step1 = (fun i j => raw8768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8768step1 raw8768step0; decide +kernel
      have hl : raw8768step1Labels = raw8768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8768step0 raw8768step0Labels permutation56 hz
    mixedMoment B raw8768step1 raw8768step1Labels = mixedMoment B raw8768step2 raw8768step2Labels := by
      have ha : raw8768step2 = (fun i j => raw8768step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8768step2 raw8768step1; decide +kernel
      have hl : raw8768step2Labels = raw8768step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8768step1 raw8768step1Labels permutation30 permutation7
    mixedMoment B raw8768step2 raw8768step2Labels = mixedMoment B raw8768step3 raw8768step3Labels := by
      have ha : raw8768step3 = raw8768step2 := by apply Matrix.ext; unfold raw8768step3 raw8768step2; decide +kernel
      have hl : raw8768step2Labels = labelEmbedding1 ∘ raw8768step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8768step2 raw8768step2Labels raw8768step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw8769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw8769step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw8769step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8769step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8769step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8769step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8769 raw8769Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw8769 raw8769Labels = mixedMoment B raw8769step0 raw8769step0Labels := by
      have hz : ∀ j, raw8769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8769step0 = (fun i j => raw8769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8769step0 raw8769; decide +kernel
      have hl : raw8769step0Labels = raw8769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8769 raw8769Labels permutation346 hz
    mixedMoment B raw8769step0 raw8769step0Labels = mixedMoment B raw8769step1 raw8769step1Labels := by
      have hz : ∀ j, raw8769step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8769step1 = (fun i j => raw8769step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8769step1 raw8769step0; decide +kernel
      have hl : raw8769step1Labels = raw8769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8769step0 raw8769step0Labels permutation56 hz
    mixedMoment B raw8769step1 raw8769step1Labels = mixedMoment B raw8769step2 raw8769step2Labels := by
      have ha : raw8769step2 = (fun i j => raw8769step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8769step2 raw8769step1; decide +kernel
      have hl : raw8769step2Labels = raw8769step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8769step1 raw8769step1Labels permutation11 permutation5
    mixedMoment B raw8769step2 raw8769step2Labels = mixedMoment B raw8769step3 raw8769step3Labels := by
      have ha : raw8769step3 = -raw8769step2 := by apply Matrix.ext; change ∀ i j, raw8769step3 i j = -(raw8769step2 i j); unfold raw8769step3 raw8769step2; decide +kernel
      have hl : raw8769step3Labels = raw8769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8769step3 raw8769step3Labels = mixedMoment B raw8769step4 raw8769step4Labels := by
      have ha : raw8769step4 = raw8769step3 := by apply Matrix.ext; unfold raw8769step4 raw8769step3; decide +kernel
      have hl : raw8769step3Labels = labelEmbedding1 ∘ raw8769step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8769step3 raw8769step3Labels raw8769step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw8770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8770 raw8770Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8770 raw8770Labels = mixedMoment B raw8770step0 raw8770step0Labels := by
      have hz : ∀ j, raw8770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8770step0 = (fun i j => raw8770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8770step0 raw8770; decide +kernel
      have hl : raw8770step0Labels = raw8770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770 raw8770Labels permutation346 hz
    mixedMoment B raw8770step0 raw8770step0Labels = mixedMoment B raw8770step1 raw8770step1Labels := by
      have hz : ∀ j, raw8770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8770step1 = (fun i j => raw8770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8770step1 raw8770step0; decide +kernel
      have hl : raw8770step1Labels = raw8770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8770step0 raw8770step0Labels permutation56 hz
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw8771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8771 raw8771Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw8771 raw8771Labels = mixedMoment B raw8771step0 raw8771step0Labels := by
      have hz : ∀ j, raw8771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8771step0 = (fun i j => raw8771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8771step0 raw8771; decide +kernel
      have hl : raw8771step0Labels = raw8771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8771 raw8771Labels permutation346 hz
    mixedMoment B raw8771step0 raw8771step0Labels = mixedMoment B raw8771step1 raw8771step1Labels := by
      have ha : raw8771step1 = (fun i j => raw8771step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8771step1 raw8771step0; decide +kernel
      have hl : raw8771step1Labels = raw8771step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8771step0 raw8771step0Labels permutation151 permutation2
    mixedMoment B raw8771step1 raw8771step1Labels = mixedMoment B raw8771step2 raw8771step2Labels := by
      have ha : raw8771step2 = -raw8771step1 := by apply Matrix.ext; change ∀ i j, raw8771step2 i j = -(raw8771step1 i j); unfold raw8771step2 raw8771step1; decide +kernel
      have hl : raw8771step2Labels = raw8771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw8772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw8772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw8772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8772 raw8772Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw8772 raw8772Labels = mixedMoment B raw8772step0 raw8772step0Labels := by
      have hz : ∀ j, raw8772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8772step0 = (fun i j => raw8772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8772step0 raw8772; decide +kernel
      have hl : raw8772step0Labels = raw8772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8772 raw8772Labels permutation265 hz
    mixedMoment B raw8772step0 raw8772step0Labels = mixedMoment B raw8772step1 raw8772step1Labels := by
      have ha : raw8772step1 = (fun i j => raw8772step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8772step1 raw8772step0; decide +kernel
      have hl : raw8772step1Labels = raw8772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8772step0 raw8772step0Labels permutation151 permutation2
    mixedMoment B raw8772step1 raw8772step1Labels = mixedMoment B raw8772step2 raw8772step2Labels := by
      have ha : raw8772step2 = -raw8772step1 := by apply Matrix.ext; change ∀ i j, raw8772step2 i j = -(raw8772step1 i j); unfold raw8772step2 raw8772step1; decide +kernel
      have hl : raw8772step2Labels = raw8772step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw8773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw8773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw8773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8773 raw8773Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw8773 raw8773Labels = mixedMoment B raw8773step0 raw8773step0Labels := by
      have hz : ∀ j, raw8773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8773step0 = (fun i j => raw8773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8773step0 raw8773; decide +kernel
      have hl : raw8773step0Labels = raw8773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8773 raw8773Labels permutation346 hz
    mixedMoment B raw8773step0 raw8773step0Labels = mixedMoment B raw8773step1 raw8773step1Labels := by
      have hz : ∀ j, raw8773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8773step1 = (fun i j => raw8773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8773step1 raw8773step0; decide +kernel
      have hl : raw8773step1Labels = raw8773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8773step0 raw8773step0Labels permutation56 hz
    mixedMoment B raw8773step1 raw8773step1Labels = mixedMoment B raw8773step2 raw8773step2Labels := by
      have ha : raw8773step2 = (fun i j => raw8773step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8773step2 raw8773step1; decide +kernel
      have hl : raw8773step2Labels = raw8773step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8773step1 raw8773step1Labels permutation31 permutation2
    mixedMoment B raw8773step2 raw8773step2Labels = mixedMoment B raw8773step3 raw8773step3Labels := by
      have ha : raw8773step3 = -raw8773step2 := by apply Matrix.ext; change ∀ i j, raw8773step3 i j = -(raw8773step2 i j); unfold raw8773step3 raw8773step2; decide +kernel
      have hl : raw8773step3Labels = raw8773step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw8774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw8774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw8774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw8774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8774 raw8774Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8774 raw8774Labels = mixedMoment B raw8774step0 raw8774step0Labels := by
      have hz : ∀ j, raw8774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8774step0 = (fun i j => raw8774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8774step0 raw8774; decide +kernel
      have hl : raw8774step0Labels = raw8774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8774 raw8774Labels permutation346 hz
    mixedMoment B raw8774step0 raw8774step0Labels = mixedMoment B raw8774step1 raw8774step1Labels := by
      have hz : ∀ j, raw8774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8774step1 = (fun i j => raw8774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8774step1 raw8774step0; decide +kernel
      have hl : raw8774step1Labels = raw8774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8774step0 raw8774step0Labels permutation56 hz
    mixedMoment B raw8774step1 raw8774step1Labels = mixedMoment B raw8774step2 raw8774step2Labels := by
      have ha : raw8774step2 = (fun i j => raw8774step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8774step2 raw8774step1; decide +kernel
      have hl : raw8774step2Labels = raw8774step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8774step1 raw8774step1Labels permutation31 permutation2
    mixedMoment B raw8774step2 raw8774step2Labels = mixedMoment B raw8774step3 raw8774step3Labels := by
      have ha : raw8774step3 = -raw8774step2 := by apply Matrix.ext; change ∀ i j, raw8774step3 i j = -(raw8774step2 i j); unfold raw8774step3 raw8774step2; decide +kernel
      have hl : raw8774step3Labels = raw8774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw8775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8775 raw8775Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8775 raw8775Labels = mixedMoment B raw8775step0 raw8775step0Labels := by
      have hz : ∀ j, raw8775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8775step0 = (fun i j => raw8775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8775step0 raw8775; decide +kernel
      have hl : raw8775step0Labels = raw8775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8775 raw8775Labels permutation346 hz
    mixedMoment B raw8775step0 raw8775step0Labels = mixedMoment B raw8775step1 raw8775step1Labels := by
      have hz : ∀ j, raw8775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8775step1 = (fun i j => raw8775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8775step1 raw8775step0; decide +kernel
      have hl : raw8775step1Labels = raw8775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8775step0 raw8775step0Labels permutation56 hz
    mixedMoment B raw8775step1 raw8775step1Labels = mixedMoment B raw8775step2 raw8775step2Labels := by
      have ha : raw8775step2 = (fun i j => raw8775step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8775step2 raw8775step1; decide +kernel
      have hl : raw8775step2Labels = raw8775step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8775step1 raw8775step1Labels permutation16 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw8776 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw8776step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8776step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8776step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical8776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8776 raw8776Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8776 raw8776Labels = mixedMoment B raw8776step0 raw8776step0Labels := by
      have hz : ∀ j, raw8776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8776step0 = (fun i j => raw8776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8776step0 raw8776; decide +kernel
      have hl : raw8776step0Labels = raw8776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776 raw8776Labels permutation346 hz
    mixedMoment B raw8776step0 raw8776step0Labels = mixedMoment B raw8776step1 raw8776step1Labels := by
      have hz : ∀ j, raw8776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8776step1 = (fun i j => raw8776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8776step1 raw8776step0; decide +kernel
      have hl : raw8776step1Labels = raw8776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776step0 raw8776step0Labels permutation56 hz
    mixedMoment B raw8776step1 raw8776step1Labels = mixedMoment B raw8776step2 raw8776step2Labels := by
      have ha : raw8776step2 = (fun i j => raw8776step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8776step2 raw8776step1; decide +kernel
      have hl : raw8776step2Labels = raw8776step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8776step1 raw8776step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw8777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8777 raw8777Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw8777 raw8777Labels = mixedMoment B raw8777step0 raw8777step0Labels := by
      have hz : ∀ j, raw8777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8777step0 = (fun i j => raw8777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8777step0 raw8777; decide +kernel
      have hl : raw8777step0Labels = raw8777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8777 raw8777Labels permutation346 hz
    mixedMoment B raw8777step0 raw8777step0Labels = mixedMoment B raw8777step1 raw8777step1Labels := by
      have ha : raw8777step1 = (fun i j => raw8777step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8777step1 raw8777step0; decide +kernel
      have hl : raw8777step1Labels = raw8777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8777step0 raw8777step0Labels permutation38 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw8778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8778 raw8778Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw8778 raw8778Labels = mixedMoment B raw8778step0 raw8778step0Labels := by
      have hz : ∀ j, raw8778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8778step0 = (fun i j => raw8778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8778step0 raw8778; decide +kernel
      have hl : raw8778step0Labels = raw8778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8778 raw8778Labels permutation265 hz
    mixedMoment B raw8778step0 raw8778step0Labels = mixedMoment B raw8778step1 raw8778step1Labels := by
      have ha : raw8778step1 = (fun i j => raw8778step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8778step1 raw8778step0; decide +kernel
      have hl : raw8778step1Labels = raw8778step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8778step0 raw8778step0Labels permutation38 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw8779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8779 raw8779Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw8779 raw8779Labels = mixedMoment B raw8779step0 raw8779step0Labels := by
      have hz : ∀ j, raw8779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8779step0 = (fun i j => raw8779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8779step0 raw8779; decide +kernel
      have hl : raw8779step0Labels = raw8779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8779 raw8779Labels permutation346 hz
    mixedMoment B raw8779step0 raw8779step0Labels = mixedMoment B raw8779step1 raw8779step1Labels := by
      have hz : ∀ j, raw8779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8779step1 = (fun i j => raw8779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8779step1 raw8779step0; decide +kernel
      have hl : raw8779step1Labels = raw8779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8779step0 raw8779step0Labels permutation56 hz
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw8780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8780 raw8780Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8780 raw8780Labels = mixedMoment B raw8780step0 raw8780step0Labels := by
      have hz : ∀ j, raw8780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8780step0 = (fun i j => raw8780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8780step0 raw8780; decide +kernel
      have hl : raw8780step0Labels = raw8780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8780 raw8780Labels permutation346 hz
    mixedMoment B raw8780step0 raw8780step0Labels = mixedMoment B raw8780step1 raw8780step1Labels := by
      have hz : ∀ j, raw8780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8780step1 = (fun i j => raw8780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8780step1 raw8780step0; decide +kernel
      have hl : raw8780step1Labels = raw8780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8780step0 raw8780step0Labels permutation56 hz
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw8781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8781 raw8781Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw8781 raw8781Labels = mixedMoment B raw8781step0 raw8781step0Labels := by
      have hz : ∀ j, raw8781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8781step0 = (fun i j => raw8781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8781step0 raw8781; decide +kernel
      have hl : raw8781step0Labels = raw8781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781 raw8781Labels permutation346 hz
    mixedMoment B raw8781step0 raw8781step0Labels = mixedMoment B raw8781step1 raw8781step1Labels := by
      have hz : ∀ j, raw8781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8781step1 = (fun i j => raw8781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8781step1 raw8781step0; decide +kernel
      have hl : raw8781step1Labels = raw8781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781step0 raw8781step0Labels permutation56 hz
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw8782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw8782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8782 raw8782Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw8782 raw8782Labels = mixedMoment B raw8782step0 raw8782step0Labels := by
      have ha : raw8782step0 = (fun i j => raw8782 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8782step0 raw8782; decide +kernel
      have hl : raw8782step0Labels = raw8782Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8782 raw8782Labels permutation158 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw8783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw8783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8783 raw8783Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw8783 raw8783Labels = mixedMoment B raw8783step0 raw8783step0Labels := by
      have hz : ∀ j, raw8783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8783step0 = (fun i j => raw8783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8783step0 raw8783; decide +kernel
      have hl : raw8783step0Labels = raw8783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8783 raw8783Labels permutation346 hz
    mixedMoment B raw8783step0 raw8783step0Labels = mixedMoment B raw8783step1 raw8783step1Labels := by
      have ha : raw8783step1 = (fun i j => raw8783step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8783step1 raw8783step0; decide +kernel
      have hl : raw8783step1Labels = raw8783step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8783step0 raw8783step0Labels permutation97 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw8784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw8784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8784 raw8784Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw8784 raw8784Labels = mixedMoment B raw8784step0 raw8784step0Labels := by
      have hz : ∀ j, raw8784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8784step0 = (fun i j => raw8784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8784step0 raw8784; decide +kernel
      have hl : raw8784step0Labels = raw8784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8784 raw8784Labels permutation346 hz
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw8785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw8785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8785 raw8785Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw8785 raw8785Labels = mixedMoment B raw8785step0 raw8785step0Labels := by
      have hz : ∀ j, raw8785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8785step0 = (fun i j => raw8785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8785step0 raw8785; decide +kernel
      have hl : raw8785step0Labels = raw8785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8785 raw8785Labels permutation346 hz
    mixedMoment B raw8785step0 raw8785step0Labels = mixedMoment B raw8785step1 raw8785step1Labels := by
      have ha : raw8785step1 = (fun i j => raw8785step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8785step1 raw8785step0; decide +kernel
      have hl : raw8785step1Labels = raw8785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8785step0 raw8785step0Labels permutation151 permutation2
    mixedMoment B raw8785step1 raw8785step1Labels = mixedMoment B raw8785step2 raw8785step2Labels := by
      have ha : raw8785step2 = -raw8785step1 := by apply Matrix.ext; change ∀ i j, raw8785step2 i j = -(raw8785step1 i j); unfold raw8785step2 raw8785step1; decide +kernel
      have hl : raw8785step2Labels = raw8785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw8786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8786step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8786 raw8786Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw8786 raw8786Labels = mixedMoment B raw8786step0 raw8786step0Labels := by
      have hz : ∀ j, raw8786 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8786step0 = (fun i j => raw8786 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8786step0 raw8786; decide +kernel
      have hl : raw8786step0Labels = raw8786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8786 raw8786Labels permutation265 hz
    mixedMoment B raw8786step0 raw8786step0Labels = mixedMoment B raw8786step1 raw8786step1Labels := by
      have ha : raw8786step1 = (fun i j => raw8786step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8786step1 raw8786step0; decide +kernel
      have hl : raw8786step1Labels = raw8786step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8786step0 raw8786step0Labels permutation38 permutation7
    mixedMoment B raw8786step1 raw8786step1Labels = mixedMoment B raw8786step2 raw8786step2Labels := by
      have ha : raw8786step2 = raw8786step1 := by apply Matrix.ext; unfold raw8786step2 raw8786step1; decide +kernel
      have hl : raw8786step1Labels = labelEmbedding10 ∘ raw8786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8786step1 raw8786step1Labels raw8786step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw8787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8787 raw8787Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw8787 raw8787Labels = mixedMoment B raw8787step0 raw8787step0Labels := by
      have hz : ∀ j, raw8787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8787step0 = (fun i j => raw8787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8787step0 raw8787; decide +kernel
      have hl : raw8787step0Labels = raw8787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8787 raw8787Labels permutation346 hz
    mixedMoment B raw8787step0 raw8787step0Labels = mixedMoment B raw8787step1 raw8787step1Labels := by
      have hz : ∀ j, raw8787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8787step1 = (fun i j => raw8787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8787step1 raw8787step0; decide +kernel
      have hl : raw8787step1Labels = raw8787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8787step0 raw8787step0Labels permutation56 hz
    mixedMoment B raw8787step1 raw8787step1Labels = mixedMoment B raw8787step2 raw8787step2Labels := by
      have ha : raw8787step2 = (fun i j => raw8787step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8787step2 raw8787step1; decide +kernel
      have hl : raw8787step2Labels = raw8787step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8787step1 raw8787step1Labels permutation31 permutation2
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw8788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8788step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8788 raw8788Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw8788 raw8788Labels = mixedMoment B raw8788step0 raw8788step0Labels := by
      have ha : raw8788step0 = (fun i j => raw8788 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8788step0 raw8788; decide +kernel
      have hl : raw8788step0Labels = raw8788Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8788 raw8788Labels permutation176 permutation6
    mixedMoment B raw8788step0 raw8788step0Labels = mixedMoment B raw8788step1 raw8788step1Labels := by
      have ha : raw8788step1 = raw8788step0 := by apply Matrix.ext; unfold raw8788step1 raw8788step0; decide +kernel
      have hl : raw8788step0Labels = labelEmbedding9 ∘ raw8788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8788step0 raw8788step0Labels raw8788step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw8789 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8789 raw8789Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8789 raw8789Labels = mixedMoment B raw8789step0 raw8789step0Labels := by
      have hz : ∀ j, raw8789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8789step0 = (fun i j => raw8789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8789step0 raw8789; decide +kernel
      have hl : raw8789step0Labels = raw8789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8789 raw8789Labels permutation346 hz
    mixedMoment B raw8789step0 raw8789step0Labels = mixedMoment B raw8789step1 raw8789step1Labels := by
      have ha : raw8789step1 = (fun i j => raw8789step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8789step1 raw8789step0; decide +kernel
      have hl : raw8789step1Labels = raw8789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8789step0 raw8789step0Labels permutation148 permutation2
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8790 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8790 raw8790Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8790 raw8790Labels = mixedMoment B raw8790step0 raw8790step0Labels := by
      have hz : ∀ j, raw8790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8790step0 = (fun i j => raw8790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8790step0 raw8790; decide +kernel
      have hl : raw8790step0Labels = raw8790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8790 raw8790Labels permutation265 hz
    mixedMoment B raw8790step0 raw8790step0Labels = mixedMoment B raw8790step1 raw8790step1Labels := by
      have ha : raw8790step1 = (fun i j => raw8790step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8790step1 raw8790step0; decide +kernel
      have hl : raw8790step1Labels = raw8790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8790step0 raw8790step0Labels permutation148 permutation2
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw8791step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8791step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8791step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8791step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8791 raw8791Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw8791 raw8791Labels = mixedMoment B raw8791step0 raw8791step0Labels := by
      have hz : ∀ j, raw8791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8791step0 = (fun i j => raw8791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8791step0 raw8791; decide +kernel
      have hl : raw8791step0Labels = raw8791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8791 raw8791Labels permutation346 hz
    mixedMoment B raw8791step0 raw8791step0Labels = mixedMoment B raw8791step1 raw8791step1Labels := by
      have hz : ∀ j, raw8791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8791step1 = (fun i j => raw8791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8791step1 raw8791step0; decide +kernel
      have hl : raw8791step1Labels = raw8791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8791step0 raw8791step0Labels permutation56 hz
    mixedMoment B raw8791step1 raw8791step1Labels = mixedMoment B raw8791step2 raw8791step2Labels := by
      have ha : raw8791step2 = (fun i j => raw8791step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8791step2 raw8791step1; decide +kernel
      have hl : raw8791step2Labels = raw8791step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8791step1 raw8791step1Labels permutation11 permutation4
    mixedMoment B raw8791step2 raw8791step2Labels = mixedMoment B raw8791step3 raw8791step3Labels := by
      have ha : raw8791step3 = -raw8791step2 := by apply Matrix.ext; change ∀ i j, raw8791step3 i j = -(raw8791step2 i j); unfold raw8791step3 raw8791step2; decide +kernel
      have hl : raw8791step3Labels = raw8791step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8791step3 raw8791step3Labels = mixedMoment B raw8791step4 raw8791step4Labels := by
      have ha : raw8791step4 = raw8791step3 := by apply Matrix.ext; unfold raw8791step4 raw8791step3; decide +kernel
      have hl : raw8791step3Labels = labelEmbedding7 ∘ raw8791step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8791step3 raw8791step3Labels raw8791step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw8792 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw8792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8792step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8792step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw8792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8792 raw8792Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw8792 raw8792Labels = mixedMoment B raw8792step0 raw8792step0Labels := by
      have hz : ∀ j, raw8792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8792step0 = (fun i j => raw8792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8792step0 raw8792; decide +kernel
      have hl : raw8792step0Labels = raw8792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8792 raw8792Labels permutation265 hz
    mixedMoment B raw8792step0 raw8792step0Labels = mixedMoment B raw8792step1 raw8792step1Labels := by
      have ha : raw8792step1 = (fun i j => raw8792step0 (permutation82 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8792step1 raw8792step0; decide +kernel
      have hl : raw8792step1Labels = raw8792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8792step0 raw8792step0Labels permutation82 permutation3
    mixedMoment B raw8792step1 raw8792step1Labels = mixedMoment B raw8792step2 raw8792step2Labels := by
      have ha : raw8792step2 = -raw8792step1 := by apply Matrix.ext; change ∀ i j, raw8792step2 i j = -(raw8792step1 i j); unfold raw8792step2 raw8792step1; decide +kernel
      have hl : raw8792step2Labels = raw8792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8792step2 raw8792step2Labels = mixedMoment B raw8792step3 raw8792step3Labels := by
      have ha : raw8792step3 = raw8792step2 := by apply Matrix.ext; unfold raw8792step3 raw8792step2; decide +kernel
      have hl : raw8792step2Labels = labelEmbedding6 ∘ raw8792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8792step2 raw8792step2Labels raw8792step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw8793 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8793step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8793step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8793step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8793step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8793 raw8793Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw8793 raw8793Labels = mixedMoment B raw8793step0 raw8793step0Labels := by
      have hz : ∀ j, raw8793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8793step0 = (fun i j => raw8793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8793step0 raw8793; decide +kernel
      have hl : raw8793step0Labels = raw8793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8793 raw8793Labels permutation346 hz
    mixedMoment B raw8793step0 raw8793step0Labels = mixedMoment B raw8793step1 raw8793step1Labels := by
      have hz : ∀ j, raw8793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8793step1 = (fun i j => raw8793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8793step1 raw8793step0; decide +kernel
      have hl : raw8793step1Labels = raw8793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8793step0 raw8793step0Labels permutation56 hz
    mixedMoment B raw8793step1 raw8793step1Labels = mixedMoment B raw8793step2 raw8793step2Labels := by
      have ha : raw8793step2 = (fun i j => raw8793step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8793step2 raw8793step1; decide +kernel
      have hl : raw8793step2Labels = raw8793step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8793step1 raw8793step1Labels permutation14 permutation3
    mixedMoment B raw8793step2 raw8793step2Labels = mixedMoment B raw8793step3 raw8793step3Labels := by
      have ha : raw8793step3 = -raw8793step2 := by apply Matrix.ext; change ∀ i j, raw8793step3 i j = -(raw8793step2 i j); unfold raw8793step3 raw8793step2; decide +kernel
      have hl : raw8793step3Labels = raw8793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8793step3 raw8793step3Labels = mixedMoment B raw8793step4 raw8793step4Labels := by
      have ha : raw8793step4 = raw8793step3 := by apply Matrix.ext; unfold raw8793step4 raw8793step3; decide +kernel
      have hl : raw8793step3Labels = labelEmbedding6 ∘ raw8793step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8793step3 raw8793step3Labels raw8793step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw8794 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8794step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8794 raw8794Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw8794 raw8794Labels = mixedMoment B raw8794step0 raw8794step0Labels := by
      have hz : ∀ j, raw8794 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8794step0 = (fun i j => raw8794 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8794step0 raw8794; decide +kernel
      have hl : raw8794step0Labels = raw8794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8794 raw8794Labels permutation265 hz
    mixedMoment B raw8794step0 raw8794step0Labels = mixedMoment B raw8794step1 raw8794step1Labels := by
      have ha : raw8794step1 = (fun i j => raw8794step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8794step1 raw8794step0; decide +kernel
      have hl : raw8794step1Labels = raw8794step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8794step0 raw8794step0Labels permutation38 permutation7
    mixedMoment B raw8794step1 raw8794step1Labels = mixedMoment B raw8794step2 raw8794step2Labels := by
      have ha : raw8794step2 = raw8794step1 := by apply Matrix.ext; unfold raw8794step2 raw8794step1; decide +kernel
      have hl : raw8794step1Labels = labelEmbedding1 ∘ raw8794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8794step1 raw8794step1Labels raw8794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw8795 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8795step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8795step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8795step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8795 raw8795Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw8795 raw8795Labels = mixedMoment B raw8795step0 raw8795step0Labels := by
      have hz : ∀ j, raw8795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8795step0 = (fun i j => raw8795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8795step0 raw8795; decide +kernel
      have hl : raw8795step0Labels = raw8795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8795 raw8795Labels permutation346 hz
    mixedMoment B raw8795step0 raw8795step0Labels = mixedMoment B raw8795step1 raw8795step1Labels := by
      have hz : ∀ j, raw8795step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8795step1 = (fun i j => raw8795step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8795step1 raw8795step0; decide +kernel
      have hl : raw8795step1Labels = raw8795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8795step0 raw8795step0Labels permutation56 hz
    mixedMoment B raw8795step1 raw8795step1Labels = mixedMoment B raw8795step2 raw8795step2Labels := by
      have ha : raw8795step2 = (fun i j => raw8795step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8795step2 raw8795step1; decide +kernel
      have hl : raw8795step2Labels = raw8795step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8795step1 raw8795step1Labels permutation8 permutation7
    mixedMoment B raw8795step2 raw8795step2Labels = mixedMoment B raw8795step3 raw8795step3Labels := by
      have ha : raw8795step3 = raw8795step2 := by apply Matrix.ext; unfold raw8795step3 raw8795step2; decide +kernel
      have hl : raw8795step2Labels = labelEmbedding1 ∘ raw8795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8795step2 raw8795step2Labels raw8795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw8796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw8796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8796 raw8796Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw8796 raw8796Labels = mixedMoment B raw8796step0 raw8796step0Labels := by
      have ha : raw8796step0 = (fun i j => raw8796 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8796step0 raw8796; decide +kernel
      have hl : raw8796step0Labels = raw8796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8796 raw8796Labels permutation200 permutation7
    mixedMoment B raw8796step0 raw8796step0Labels = mixedMoment B raw8796step1 raw8796step1Labels := by
      have ha : raw8796step1 = raw8796step0 := by apply Matrix.ext; unfold raw8796step1 raw8796step0; decide +kernel
      have hl : raw8796step0Labels = labelEmbedding1 ∘ raw8796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8796step0 raw8796step0Labels raw8796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw8797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8797 raw8797Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8797 raw8797Labels = mixedMoment B raw8797step0 raw8797step0Labels := by
      have hz : ∀ j, raw8797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8797step0 = (fun i j => raw8797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8797step0 raw8797; decide +kernel
      have hl : raw8797step0Labels = raw8797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8797 raw8797Labels permutation346 hz
    mixedMoment B raw8797step0 raw8797step0Labels = mixedMoment B raw8797step1 raw8797step1Labels := by
      have ha : raw8797step1 = (fun i j => raw8797step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8797step1 raw8797step0; decide +kernel
      have hl : raw8797step1Labels = raw8797step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8797step0 raw8797step0Labels permutation38 permutation7
    mixedMoment B raw8797step1 raw8797step1Labels = mixedMoment B raw8797step2 raw8797step2Labels := by
      have ha : raw8797step2 = raw8797step1 := by apply Matrix.ext; unfold raw8797step2 raw8797step1; decide +kernel
      have hl : raw8797step1Labels = labelEmbedding1 ∘ raw8797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8797step1 raw8797step1Labels raw8797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8798 raw8798Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8798 raw8798Labels = mixedMoment B raw8798step0 raw8798step0Labels := by
      have hz : ∀ j, raw8798 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8798step0 = (fun i j => raw8798 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8798step0 raw8798; decide +kernel
      have hl : raw8798step0Labels = raw8798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8798 raw8798Labels permutation265 hz
    mixedMoment B raw8798step0 raw8798step0Labels = mixedMoment B raw8798step1 raw8798step1Labels := by
      have ha : raw8798step1 = (fun i j => raw8798step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8798step1 raw8798step0; decide +kernel
      have hl : raw8798step1Labels = raw8798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8798step0 raw8798step0Labels permutation38 permutation7
    mixedMoment B raw8798step1 raw8798step1Labels = mixedMoment B raw8798step2 raw8798step2Labels := by
      have ha : raw8798step2 = raw8798step1 := by apply Matrix.ext; unfold raw8798step2 raw8798step1; decide +kernel
      have hl : raw8798step1Labels = labelEmbedding1 ∘ raw8798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8798step1 raw8798step1Labels raw8798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8799 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8799step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw8799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8799 raw8799Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw8799 raw8799Labels = mixedMoment B raw8799step0 raw8799step0Labels := by
      have hz : ∀ j, raw8799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8799step0 = (fun i j => raw8799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8799step0 raw8799; decide +kernel
      have hl : raw8799step0Labels = raw8799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8799 raw8799Labels permutation346 hz
    mixedMoment B raw8799step0 raw8799step0Labels = mixedMoment B raw8799step1 raw8799step1Labels := by
      have hz : ∀ j, raw8799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8799step1 = (fun i j => raw8799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8799step1 raw8799step0; decide +kernel
      have hl : raw8799step1Labels = raw8799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8799step0 raw8799step0Labels permutation56 hz
    mixedMoment B raw8799step1 raw8799step1Labels = mixedMoment B raw8799step2 raw8799step2Labels := by
      have ha : raw8799step2 = (fun i j => raw8799step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8799step2 raw8799step1; decide +kernel
      have hl : raw8799step2Labels = raw8799step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8799step1 raw8799step1Labels permutation17 permutation5
    mixedMoment B raw8799step2 raw8799step2Labels = mixedMoment B raw8799step3 raw8799step3Labels := by
      have ha : raw8799step3 = raw8799step2 := by apply Matrix.ext; unfold raw8799step3 raw8799step2; decide +kernel
      have hl : raw8799step2Labels = labelEmbedding1 ∘ raw8799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8799step2 raw8799step2Labels raw8799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw8800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw8800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw8800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw8800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8800 raw8800Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw8800 raw8800Labels = mixedMoment B raw8800step0 raw8800step0Labels := by
      have hz : ∀ j, raw8800 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8800step0 = (fun i j => raw8800 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8800step0 raw8800; decide +kernel
      have hl : raw8800step0Labels = raw8800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8800 raw8800Labels permutation265 hz
    mixedMoment B raw8800step0 raw8800step0Labels = mixedMoment B raw8800step1 raw8800step1Labels := by
      have ha : raw8800step1 = (fun i j => raw8800step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8800step1 raw8800step0; decide +kernel
      have hl : raw8800step1Labels = raw8800step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8800step0 raw8800step0Labels permutation97 permutation5
    mixedMoment B raw8800step1 raw8800step1Labels = mixedMoment B raw8800step2 raw8800step2Labels := by
      have ha : raw8800step2 = raw8800step1 := by apply Matrix.ext; unfold raw8800step2 raw8800step1; decide +kernel
      have hl : raw8800step1Labels = labelEmbedding1 ∘ raw8800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8800step1 raw8800step1Labels raw8800step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw8801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw8801step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8801step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8801step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8801 raw8801Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw8801 raw8801Labels = mixedMoment B raw8801step0 raw8801step0Labels := by
      have hz : ∀ j, raw8801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8801step0 = (fun i j => raw8801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8801step0 raw8801; decide +kernel
      have hl : raw8801step0Labels = raw8801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8801 raw8801Labels permutation346 hz
    mixedMoment B raw8801step0 raw8801step0Labels = mixedMoment B raw8801step1 raw8801step1Labels := by
      have hz : ∀ j, raw8801step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8801step1 = (fun i j => raw8801step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8801step1 raw8801step0; decide +kernel
      have hl : raw8801step1Labels = raw8801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8801step0 raw8801step0Labels permutation56 hz
    mixedMoment B raw8801step1 raw8801step1Labels = mixedMoment B raw8801step2 raw8801step2Labels := by
      have ha : raw8801step2 = (fun i j => raw8801step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8801step2 raw8801step1; decide +kernel
      have hl : raw8801step2Labels = raw8801step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8801step1 raw8801step1Labels permutation17 permutation5
    mixedMoment B raw8801step2 raw8801step2Labels = mixedMoment B raw8801step3 raw8801step3Labels := by
      have ha : raw8801step3 = raw8801step2 := by apply Matrix.ext; unfold raw8801step3 raw8801step2; decide +kernel
      have hl : raw8801step2Labels = labelEmbedding1 ∘ raw8801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8801step2 raw8801step2Labels raw8801step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw8802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8802 raw8802Labels = mixedMoment B node5429 node5429Labels := by
  calc
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw8803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8803 raw8803Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8803 raw8803Labels = mixedMoment B raw8803step0 raw8803step0Labels := by
      have hz : ∀ j, raw8803 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8803step0 = (fun i j => raw8803 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8803step0 raw8803; decide +kernel
      have hl : raw8803step0Labels = raw8803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8803 raw8803Labels permutation265 hz
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw8804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8804 raw8804Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw8804 raw8804Labels = mixedMoment B raw8804step0 raw8804step0Labels := by
      have hz : ∀ j, raw8804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8804step0 = (fun i j => raw8804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8804step0 raw8804; decide +kernel
      have hl : raw8804step0Labels = raw8804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8804 raw8804Labels permutation265 hz
    mixedMoment B raw8804step0 raw8804step0Labels = mixedMoment B raw8804step1 raw8804step1Labels := by
      have ha : raw8804step1 = (fun i j => raw8804step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8804step1 raw8804step0; decide +kernel
      have hl : raw8804step1Labels = raw8804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8804step0 raw8804step0Labels permutation38 permutation2
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw8805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw8805step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8805step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw8805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8805 raw8805Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw8805 raw8805Labels = mixedMoment B raw8805step0 raw8805step0Labels := by
      have hz : ∀ j, raw8805 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8805step0 = (fun i j => raw8805 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8805step0 raw8805; decide +kernel
      have hl : raw8805step0Labels = raw8805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8805 raw8805Labels permutation265 hz
    mixedMoment B raw8805step0 raw8805step0Labels = mixedMoment B raw8805step1 raw8805step1Labels := by
      have ha : raw8805step1 = (fun i j => raw8805step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8805step1 raw8805step0; decide +kernel
      have hl : raw8805step1Labels = raw8805step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8805step0 raw8805step0Labels permutation44 permutation7
    mixedMoment B raw8805step1 raw8805step1Labels = mixedMoment B raw8805step2 raw8805step2Labels := by
      have ha : raw8805step2 = -raw8805step1 := by apply Matrix.ext; change ∀ i j, raw8805step2 i j = -(raw8805step1 i j); unfold raw8805step2 raw8805step1; decide +kernel
      have hl : raw8805step2Labels = raw8805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8805step2 raw8805step2Labels = mixedMoment B raw8805step3 raw8805step3Labels := by
      have ha : raw8805step3 = raw8805step2 := by apply Matrix.ext; unfold raw8805step3 raw8805step2; decide +kernel
      have hl : raw8805step2Labels = labelEmbedding10 ∘ raw8805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8805step2 raw8805step2Labels raw8805step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw8806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw8806step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8806step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw8806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8806 raw8806Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw8806 raw8806Labels = mixedMoment B raw8806step0 raw8806step0Labels := by
      have hz : ∀ j, raw8806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8806step0 = (fun i j => raw8806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8806step0 raw8806; decide +kernel
      have hl : raw8806step0Labels = raw8806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8806 raw8806Labels permutation265 hz
    mixedMoment B raw8806step0 raw8806step0Labels = mixedMoment B raw8806step1 raw8806step1Labels := by
      have ha : raw8806step1 = (fun i j => raw8806step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8806step1 raw8806step0; decide +kernel
      have hl : raw8806step1Labels = raw8806step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8806step0 raw8806step0Labels permutation44 permutation7
    mixedMoment B raw8806step1 raw8806step1Labels = mixedMoment B raw8806step2 raw8806step2Labels := by
      have ha : raw8806step2 = -raw8806step1 := by apply Matrix.ext; change ∀ i j, raw8806step2 i j = -(raw8806step1 i j); unfold raw8806step2 raw8806step1; decide +kernel
      have hl : raw8806step2Labels = raw8806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8806step2 raw8806step2Labels = mixedMoment B raw8806step3 raw8806step3Labels := by
      have ha : raw8806step3 = raw8806step2 := by apply Matrix.ext; unfold raw8806step3 raw8806step2; decide +kernel
      have hl : raw8806step2Labels = labelEmbedding10 ∘ raw8806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8806step2 raw8806step2Labels raw8806step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw8807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8807step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw8807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8807 raw8807Labels = mixedMoment B node4582 node4582Labels := by
  calc
    mixedMoment B raw8807 raw8807Labels = mixedMoment B raw8807step0 raw8807step0Labels := by
      have ha : raw8807step0 = (fun i j => raw8807 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8807step0 raw8807; decide +kernel
      have hl : raw8807step0Labels = raw8807Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8807 raw8807Labels permutation182 permutation3
    mixedMoment B raw8807step0 raw8807step0Labels = mixedMoment B raw8807step1 raw8807step1Labels := by
      have ha : raw8807step1 = raw8807step0 := by apply Matrix.ext; unfold raw8807step1 raw8807step0; decide +kernel
      have hl : raw8807step0Labels = labelEmbedding6 ∘ raw8807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8807step0 raw8807step0Labels raw8807step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4582 node4582Labels := by rfl

def raw8808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8808 raw8808Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw8808 raw8808Labels = mixedMoment B raw8808step0 raw8808step0Labels := by
      have ha : raw8808step0 = (fun i j => raw8808 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8808step0 raw8808; decide +kernel
      have hl : raw8808step0Labels = raw8808Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8808 raw8808Labels permutation184 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw8809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw8809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8809 raw8809Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw8809 raw8809Labels = mixedMoment B raw8809step0 raw8809step0Labels := by
      have ha : raw8809step0 = (fun i j => raw8809 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8809step0 raw8809; decide +kernel
      have hl : raw8809step0Labels = raw8809Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8809 raw8809Labels permutation208 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw8810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8810 raw8810Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw8810 raw8810Labels = mixedMoment B raw8810step0 raw8810step0Labels := by
      have ha : raw8810step0 = (fun i j => raw8810 (permutation232 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8810step0 raw8810; decide +kernel
      have hl : raw8810step0Labels = raw8810Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8810 raw8810Labels permutation232 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw8811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8811 raw8811Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw8811 raw8811Labels = mixedMoment B raw8811step0 raw8811step0Labels := by
      have ha : raw8811step0 = (fun i j => raw8811 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8811step0 raw8811; decide +kernel
      have hl : raw8811step0Labels = raw8811Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8811 raw8811Labels permutation184 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw8812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8812step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8812 raw8812Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw8812 raw8812Labels = mixedMoment B raw8812step0 raw8812step0Labels := by
      have hz : ∀ j, raw8812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8812step0 = (fun i j => raw8812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8812step0 raw8812; decide +kernel
      have hl : raw8812step0Labels = raw8812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8812 raw8812Labels permutation265 hz
    mixedMoment B raw8812step0 raw8812step0Labels = mixedMoment B raw8812step1 raw8812step1Labels := by
      have ha : raw8812step1 = (fun i j => raw8812step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8812step1 raw8812step0; decide +kernel
      have hl : raw8812step1Labels = raw8812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8812step0 raw8812step0Labels permutation38 permutation3
    mixedMoment B raw8812step1 raw8812step1Labels = mixedMoment B raw8812step2 raw8812step2Labels := by
      have ha : raw8812step2 = raw8812step1 := by apply Matrix.ext; unfold raw8812step2 raw8812step1; decide +kernel
      have hl : raw8812step1Labels = labelEmbedding6 ∘ raw8812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8812step1 raw8812step1Labels raw8812step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw8813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8813 raw8813Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8813 raw8813Labels = mixedMoment B raw8813step0 raw8813step0Labels := by
      have ha : raw8813step0 = (fun i j => raw8813 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8813step0 raw8813; decide +kernel
      have hl : raw8813step0Labels = raw8813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8813 raw8813Labels permutation160 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw8814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8814 raw8814Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw8814 raw8814Labels = mixedMoment B raw8814step0 raw8814step0Labels := by
      have hz : ∀ j, raw8814 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8814step0 = (fun i j => raw8814 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8814step0 raw8814; decide +kernel
      have hl : raw8814step0Labels = raw8814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8814 raw8814Labels permutation265 hz
    mixedMoment B raw8814step0 raw8814step0Labels = mixedMoment B raw8814step1 raw8814step1Labels := by
      have ha : raw8814step1 = (fun i j => raw8814step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8814step1 raw8814step0; decide +kernel
      have hl : raw8814step1Labels = raw8814step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8814step0 raw8814step0Labels permutation40 permutation2
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw8815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8815 raw8815Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw8815 raw8815Labels = mixedMoment B raw8815step0 raw8815step0Labels := by
      have hz : ∀ j, raw8815 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8815step0 = (fun i j => raw8815 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8815step0 raw8815; decide +kernel
      have hl : raw8815step0Labels = raw8815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8815 raw8815Labels permutation265 hz
    mixedMoment B raw8815step0 raw8815step0Labels = mixedMoment B raw8815step1 raw8815step1Labels := by
      have ha : raw8815step1 = (fun i j => raw8815step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8815step1 raw8815step0; decide +kernel
      have hl : raw8815step1Labels = raw8815step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8815step0 raw8815step0Labels permutation46 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw8816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8816 raw8816Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw8816 raw8816Labels = mixedMoment B raw8816step0 raw8816step0Labels := by
      have hz : ∀ j, raw8816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8816step0 = (fun i j => raw8816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8816step0 raw8816; decide +kernel
      have hl : raw8816step0Labels = raw8816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8816 raw8816Labels permutation265 hz
    mixedMoment B raw8816step0 raw8816step0Labels = mixedMoment B raw8816step1 raw8816step1Labels := by
      have ha : raw8816step1 = (fun i j => raw8816step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8816step1 raw8816step0; decide +kernel
      have hl : raw8816step1Labels = raw8816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8816step0 raw8816step0Labels permutation40 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw8817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8817step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw8817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8817 raw8817Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw8817 raw8817Labels = mixedMoment B raw8817step0 raw8817step0Labels := by
      have hz : ∀ j, raw8817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8817step0 = (fun i j => raw8817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8817step0 raw8817; decide +kernel
      have hl : raw8817step0Labels = raw8817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8817 raw8817Labels permutation265 hz
    mixedMoment B raw8817step0 raw8817step0Labels = mixedMoment B raw8817step1 raw8817step1Labels := by
      have ha : raw8817step1 = (fun i j => raw8817step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8817step1 raw8817step0; decide +kernel
      have hl : raw8817step1Labels = raw8817step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8817step0 raw8817step0Labels permutation32 permutation3
    mixedMoment B raw8817step1 raw8817step1Labels = mixedMoment B raw8817step2 raw8817step2Labels := by
      have ha : raw8817step2 = raw8817step1 := by apply Matrix.ext; unfold raw8817step2 raw8817step1; decide +kernel
      have hl : raw8817step1Labels = labelEmbedding6 ∘ raw8817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8817step1 raw8817step1Labels raw8817step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw8818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8818 raw8818Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw8818 raw8818Labels = mixedMoment B raw8818step0 raw8818step0Labels := by
      have ha : raw8818step0 = (fun i j => raw8818 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8818step0 raw8818; decide +kernel
      have hl : raw8818step0Labels = raw8818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8818 raw8818Labels permutation154 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw8819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw8819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw8819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8819 raw8819Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw8819 raw8819Labels = mixedMoment B raw8819step0 raw8819step0Labels := by
      have hz : ∀ j, raw8819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8819step0 = (fun i j => raw8819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8819step0 raw8819; decide +kernel
      have hl : raw8819step0Labels = raw8819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8819 raw8819Labels permutation265 hz
    mixedMoment B raw8819step0 raw8819step0Labels = mixedMoment B raw8819step1 raw8819step1Labels := by
      have ha : raw8819step1 = (fun i j => raw8819step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8819step1 raw8819step0; decide +kernel
      have hl : raw8819step1Labels = raw8819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8819step0 raw8819step0Labels permutation34 permutation2
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw8820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw8820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8820 raw8820Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw8820 raw8820Labels = mixedMoment B raw8820step0 raw8820step0Labels := by
      have hz : ∀ j, raw8820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8820step0 = (fun i j => raw8820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8820step0 raw8820; decide +kernel
      have hl : raw8820step0Labels = raw8820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8820 raw8820Labels permutation265 hz
    mixedMoment B raw8820step0 raw8820step0Labels = mixedMoment B raw8820step1 raw8820step1Labels := by
      have ha : raw8820step1 = (fun i j => raw8820step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8820step1 raw8820step0; decide +kernel
      have hl : raw8820step1Labels = raw8820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8820step0 raw8820step0Labels permutation44 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw8821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw8821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw8821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8821 raw8821Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw8821 raw8821Labels = mixedMoment B raw8821step0 raw8821step0Labels := by
      have hz : ∀ j, raw8821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8821step0 = (fun i j => raw8821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8821step0 raw8821; decide +kernel
      have hl : raw8821step0Labels = raw8821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8821 raw8821Labels permutation265 hz
    mixedMoment B raw8821step0 raw8821step0Labels = mixedMoment B raw8821step1 raw8821step1Labels := by
      have ha : raw8821step1 = (fun i j => raw8821step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8821step1 raw8821step0; decide +kernel
      have hl : raw8821step1Labels = raw8821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8821step0 raw8821step0Labels permutation34 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw8822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8822step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw8822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8822 raw8822Labels = mixedMoment B node4585 node4585Labels := by
  calc
    mixedMoment B raw8822 raw8822Labels = mixedMoment B raw8822step0 raw8822step0Labels := by
      have hz : ∀ j, raw8822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8822step0 = (fun i j => raw8822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8822step0 raw8822; decide +kernel
      have hl : raw8822step0Labels = raw8822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8822 raw8822Labels permutation265 hz
    mixedMoment B raw8822step0 raw8822step0Labels = mixedMoment B raw8822step1 raw8822step1Labels := by
      have ha : raw8822step1 = (fun i j => raw8822step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8822step1 raw8822step0; decide +kernel
      have hl : raw8822step1Labels = raw8822step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8822step0 raw8822step0Labels permutation33 permutation3
    mixedMoment B raw8822step1 raw8822step1Labels = mixedMoment B raw8822step2 raw8822step2Labels := by
      have ha : raw8822step2 = raw8822step1 := by apply Matrix.ext; unfold raw8822step2 raw8822step1; decide +kernel
      have hl : raw8822step1Labels = labelEmbedding6 ∘ raw8822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8822step1 raw8822step1Labels raw8822step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4585 node4585Labels := by rfl

def raw8823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8823step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8823 raw8823Labels = mixedMoment B node5011 node5011Labels := by
  calc
    mixedMoment B raw8823 raw8823Labels = mixedMoment B raw8823step0 raw8823step0Labels := by
      have ha : raw8823step0 = (fun i j => raw8823 (permutation584 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8823step0 raw8823; decide +kernel
      have hl : raw8823step0Labels = raw8823Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8823 raw8823Labels permutation584 permutation5
    mixedMoment B raw8823step0 raw8823step0Labels = mixedMoment B raw8823step1 raw8823step1Labels := by
      have ha : raw8823step1 = raw8823step0 := by apply Matrix.ext; unfold raw8823step1 raw8823step0; decide +kernel
      have hl : raw8823step0Labels = labelEmbedding8 ∘ raw8823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8823step0 raw8823step0Labels raw8823step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5011 node5011Labels := by rfl

def raw8824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8824step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8824 raw8824Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw8824 raw8824Labels = mixedMoment B raw8824step0 raw8824step0Labels := by
      have hz : ∀ j, raw8824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8824step0 = (fun i j => raw8824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8824step0 raw8824; decide +kernel
      have hl : raw8824step0Labels = raw8824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8824 raw8824Labels permutation265 hz
    mixedMoment B raw8824step0 raw8824step0Labels = mixedMoment B raw8824step1 raw8824step1Labels := by
      have ha : raw8824step1 = (fun i j => raw8824step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8824step1 raw8824step0; decide +kernel
      have hl : raw8824step1Labels = raw8824step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8824step0 raw8824step0Labels permutation126 permutation5
    mixedMoment B raw8824step1 raw8824step1Labels = mixedMoment B raw8824step2 raw8824step2Labels := by
      have ha : raw8824step2 = raw8824step1 := by apply Matrix.ext; unfold raw8824step2 raw8824step1; decide +kernel
      have hl : raw8824step1Labels = labelEmbedding8 ∘ raw8824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8824step1 raw8824step1Labels raw8824step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw8825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw8825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8825step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw8825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8825 raw8825Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw8825 raw8825Labels = mixedMoment B raw8825step0 raw8825step0Labels := by
      have hz : ∀ j, raw8825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8825step0 = (fun i j => raw8825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8825step0 raw8825; decide +kernel
      have hl : raw8825step0Labels = raw8825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8825 raw8825Labels permutation265 hz
    mixedMoment B raw8825step0 raw8825step0Labels = mixedMoment B raw8825step1 raw8825step1Labels := by
      have ha : raw8825step1 = (fun i j => raw8825step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8825step1 raw8825step0; decide +kernel
      have hl : raw8825step1Labels = raw8825step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8825step0 raw8825step0Labels permutation124 permutation5
    mixedMoment B raw8825step1 raw8825step1Labels = mixedMoment B raw8825step2 raw8825step2Labels := by
      have ha : raw8825step2 = raw8825step1 := by apply Matrix.ext; unfold raw8825step2 raw8825step1; decide +kernel
      have hl : raw8825step1Labels = labelEmbedding8 ∘ raw8825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8825step1 raw8825step1Labels raw8825step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw8826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw8826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8826step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8826 raw8826Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw8826 raw8826Labels = mixedMoment B raw8826step0 raw8826step0Labels := by
      have hz : ∀ j, raw8826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8826step0 = (fun i j => raw8826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8826step0 raw8826; decide +kernel
      have hl : raw8826step0Labels = raw8826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8826 raw8826Labels permutation265 hz
    mixedMoment B raw8826step0 raw8826step0Labels = mixedMoment B raw8826step1 raw8826step1Labels := by
      have ha : raw8826step1 = (fun i j => raw8826step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8826step1 raw8826step0; decide +kernel
      have hl : raw8826step1Labels = raw8826step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8826step0 raw8826step0Labels permutation125 permutation5
    mixedMoment B raw8826step1 raw8826step1Labels = mixedMoment B raw8826step2 raw8826step2Labels := by
      have ha : raw8826step2 = raw8826step1 := by apply Matrix.ext; unfold raw8826step2 raw8826step1; decide +kernel
      have hl : raw8826step1Labels = labelEmbedding8 ∘ raw8826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8826step1 raw8826step1Labels raw8826step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw8827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw8827step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw8827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8827 raw8827Labels = mixedMoment B node4584 node4584Labels := by
  calc
    mixedMoment B raw8827 raw8827Labels = mixedMoment B raw8827step0 raw8827step0Labels := by
      have hz : ∀ j, raw8827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8827step0 = (fun i j => raw8827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8827step0 raw8827; decide +kernel
      have hl : raw8827step0Labels = raw8827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8827 raw8827Labels permutation265 hz
    mixedMoment B raw8827step0 raw8827step0Labels = mixedMoment B raw8827step1 raw8827step1Labels := by
      have ha : raw8827step1 = (fun i j => raw8827step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8827step1 raw8827step0; decide +kernel
      have hl : raw8827step1Labels = raw8827step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8827step0 raw8827step0Labels permutation32 permutation3
    mixedMoment B raw8827step1 raw8827step1Labels = mixedMoment B raw8827step2 raw8827step2Labels := by
      have ha : raw8827step2 = raw8827step1 := by apply Matrix.ext; unfold raw8827step2 raw8827step1; decide +kernel
      have hl : raw8827step1Labels = labelEmbedding6 ∘ raw8827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8827step1 raw8827step1Labels raw8827step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4584 node4584Labels := by rfl

def raw8828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8828step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8828step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8828step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8828 raw8828Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw8828 raw8828Labels = mixedMoment B raw8828step0 raw8828step0Labels := by
      have ha : raw8828step0 = (fun i j => raw8828 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8828step0 raw8828; decide +kernel
      have hl : raw8828step0Labels = raw8828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8828 raw8828Labels permutation682 permutation3
    mixedMoment B raw8828step0 raw8828step0Labels = mixedMoment B raw8828step1 raw8828step1Labels := by
      have ha : raw8828step1 = -raw8828step0 := by apply Matrix.ext; change ∀ i j, raw8828step1 i j = -(raw8828step0 i j); unfold raw8828step1 raw8828step0; decide +kernel
      have hl : raw8828step1Labels = raw8828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8828step1 raw8828step1Labels = mixedMoment B raw8828step2 raw8828step2Labels := by
      have ha : raw8828step2 = raw8828step1 := by apply Matrix.ext; unfold raw8828step2 raw8828step1; decide +kernel
      have hl : raw8828step1Labels = labelEmbedding6 ∘ raw8828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8828step1 raw8828step1Labels raw8828step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

def raw8829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8829step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8829step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8829step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8829 raw8829Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw8829 raw8829Labels = mixedMoment B raw8829step0 raw8829step0Labels := by
      have hz : ∀ j, raw8829 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8829step0 = (fun i j => raw8829 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8829step0 raw8829; decide +kernel
      have hl : raw8829step0Labels = raw8829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8829 raw8829Labels permutation265 hz
    mixedMoment B raw8829step0 raw8829step0Labels = mixedMoment B raw8829step1 raw8829step1Labels := by
      have ha : raw8829step1 = (fun i j => raw8829step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8829step1 raw8829step0; decide +kernel
      have hl : raw8829step1Labels = raw8829step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8829step0 raw8829step0Labels permutation151 permutation3
    mixedMoment B raw8829step1 raw8829step1Labels = mixedMoment B raw8829step2 raw8829step2Labels := by
      have ha : raw8829step2 = -raw8829step1 := by apply Matrix.ext; change ∀ i j, raw8829step2 i j = -(raw8829step1 i j); unfold raw8829step2 raw8829step1; decide +kernel
      have hl : raw8829step2Labels = raw8829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8829step2 raw8829step2Labels = mixedMoment B raw8829step3 raw8829step3Labels := by
      have ha : raw8829step3 = raw8829step2 := by apply Matrix.ext; unfold raw8829step3 raw8829step2; decide +kernel
      have hl : raw8829step2Labels = labelEmbedding6 ∘ raw8829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8829step2 raw8829step2Labels raw8829step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw8830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw8830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8830step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8830step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8830step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8830step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8830 raw8830Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw8830 raw8830Labels = mixedMoment B raw8830step0 raw8830step0Labels := by
      have hz : ∀ j, raw8830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8830step0 = (fun i j => raw8830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8830step0 raw8830; decide +kernel
      have hl : raw8830step0Labels = raw8830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8830 raw8830Labels permutation265 hz
    mixedMoment B raw8830step0 raw8830step0Labels = mixedMoment B raw8830step1 raw8830step1Labels := by
      have ha : raw8830step1 = (fun i j => raw8830step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8830step1 raw8830step0; decide +kernel
      have hl : raw8830step1Labels = raw8830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8830step0 raw8830step0Labels permutation149 permutation3
    mixedMoment B raw8830step1 raw8830step1Labels = mixedMoment B raw8830step2 raw8830step2Labels := by
      have ha : raw8830step2 = -raw8830step1 := by apply Matrix.ext; change ∀ i j, raw8830step2 i j = -(raw8830step1 i j); unfold raw8830step2 raw8830step1; decide +kernel
      have hl : raw8830step2Labels = raw8830step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8830step2 raw8830step2Labels = mixedMoment B raw8830step3 raw8830step3Labels := by
      have ha : raw8830step3 = raw8830step2 := by apply Matrix.ext; unfold raw8830step3 raw8830step2; decide +kernel
      have hl : raw8830step2Labels = labelEmbedding6 ∘ raw8830step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8830step2 raw8830step2Labels raw8830step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw8831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw8831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw8831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8831 raw8831Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw8831 raw8831Labels = mixedMoment B raw8831step0 raw8831step0Labels := by
      have hz : ∀ j, raw8831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8831step0 = (fun i j => raw8831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8831step0 raw8831; decide +kernel
      have hl : raw8831step0Labels = raw8831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8831 raw8831Labels permutation265 hz
    mixedMoment B raw8831step0 raw8831step0Labels = mixedMoment B raw8831step1 raw8831step1Labels := by
      have ha : raw8831step1 = (fun i j => raw8831step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8831step1 raw8831step0; decide +kernel
      have hl : raw8831step1Labels = raw8831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8831step0 raw8831step0Labels permutation44 permutation2
    _ = mixedMoment B node5252 node5252Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
