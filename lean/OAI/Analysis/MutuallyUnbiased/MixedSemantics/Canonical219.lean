import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28032 raw28032Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw28032 raw28032Labels = mixedMoment B raw28032step0 raw28032step0Labels := by
      have ha : raw28032step0 = (fun i j => raw28032 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28032step0 raw28032; decide +kernel
      have hl : raw28032step0Labels = raw28032Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28032 raw28032Labels permutation644 permutation2
    mixedMoment B raw28032step0 raw28032step0Labels = mixedMoment B raw28032step1 raw28032step1Labels := by
      have ha : raw28032step1 = -raw28032step0 := by apply Matrix.ext; change ∀ i j, raw28032step1 i j = -(raw28032step0 i j); unfold raw28032step1 raw28032step0; decide +kernel
      have hl : raw28032step1Labels = raw28032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4764 node4764Labels := by rfl

def raw28033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28033 raw28033Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw28033 raw28033Labels = mixedMoment B raw28033step0 raw28033step0Labels := by
      have hz : ∀ j, raw28033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28033step0 = (fun i j => raw28033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28033step0 raw28033; decide +kernel
      have hl : raw28033step0Labels = raw28033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28033 raw28033Labels permutation520 hz
    mixedMoment B raw28033step0 raw28033step0Labels = mixedMoment B raw28033step1 raw28033step1Labels := by
      have ha : raw28033step1 = (fun i j => raw28033step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28033step1 raw28033step0; decide +kernel
      have hl : raw28033step1Labels = raw28033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28033step0 raw28033step0Labels permutation145 permutation2
    mixedMoment B raw28033step1 raw28033step1Labels = mixedMoment B raw28033step2 raw28033step2Labels := by
      have ha : raw28033step2 = -raw28033step1 := by apply Matrix.ext; change ∀ i j, raw28033step2 i j = -(raw28033step1 i j); unfold raw28033step2 raw28033step1; decide +kernel
      have hl : raw28033step2Labels = raw28033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw28034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28034 raw28034Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw28034 raw28034Labels = mixedMoment B raw28034step0 raw28034step0Labels := by
      have ha : raw28034step0 = (fun i j => raw28034 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28034step0 raw28034; decide +kernel
      have hl : raw28034step0Labels = raw28034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28034 raw28034Labels permutation158 permutation3
    mixedMoment B raw28034step0 raw28034step0Labels = mixedMoment B raw28034step1 raw28034step1Labels := by
      have ha : raw28034step1 = raw28034step0 := by apply Matrix.ext; unfold raw28034step1 raw28034step0; decide +kernel
      have hl : raw28034step0Labels = labelEmbedding6 ∘ raw28034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28034step0 raw28034step0Labels raw28034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw28035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28035 raw28035Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw28035 raw28035Labels = mixedMoment B raw28035step0 raw28035step0Labels := by
      have hz : ∀ j, raw28035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28035step0 = (fun i j => raw28035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28035step0 raw28035; decide +kernel
      have hl : raw28035step0Labels = raw28035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28035 raw28035Labels permutation346 hz
    mixedMoment B raw28035step0 raw28035step0Labels = mixedMoment B raw28035step1 raw28035step1Labels := by
      have ha : raw28035step1 = (fun i j => raw28035step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28035step1 raw28035step0; decide +kernel
      have hl : raw28035step1Labels = raw28035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28035step0 raw28035step0Labels permutation34 permutation3
    mixedMoment B raw28035step1 raw28035step1Labels = mixedMoment B raw28035step2 raw28035step2Labels := by
      have ha : raw28035step2 = raw28035step1 := by apply Matrix.ext; unfold raw28035step2 raw28035step1; decide +kernel
      have hl : raw28035step1Labels = labelEmbedding6 ∘ raw28035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28035step1 raw28035step1Labels raw28035step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4353 node4353Labels := by rfl

def raw28036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28036 raw28036Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw28036 raw28036Labels = mixedMoment B raw28036step0 raw28036step0Labels := by
      have hz : ∀ j, raw28036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28036step0 = (fun i j => raw28036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28036step0 raw28036; decide +kernel
      have hl : raw28036step0Labels = raw28036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28036 raw28036Labels permutation346 hz
    mixedMoment B raw28036step0 raw28036step0Labels = mixedMoment B raw28036step1 raw28036step1Labels := by
      have ha : raw28036step1 = (fun i j => raw28036step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28036step1 raw28036step0; decide +kernel
      have hl : raw28036step1Labels = raw28036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28036step0 raw28036step0Labels permutation151 permutation2
    mixedMoment B raw28036step1 raw28036step1Labels = mixedMoment B raw28036step2 raw28036step2Labels := by
      have ha : raw28036step2 = -raw28036step1 := by apply Matrix.ext; change ∀ i j, raw28036step2 i j = -(raw28036step1 i j); unfold raw28036step2 raw28036step1; decide +kernel
      have hl : raw28036step2Labels = raw28036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw28037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28037 raw28037Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw28037 raw28037Labels = mixedMoment B raw28037step0 raw28037step0Labels := by
      have ha : raw28037step0 = (fun i j => raw28037 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28037step0 raw28037; decide +kernel
      have hl : raw28037step0Labels = raw28037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28037 raw28037Labels permutation688 permutation2
    mixedMoment B raw28037step0 raw28037step0Labels = mixedMoment B raw28037step1 raw28037step1Labels := by
      have ha : raw28037step1 = -raw28037step0 := by apply Matrix.ext; change ∀ i j, raw28037step1 i j = -(raw28037step0 i j); unfold raw28037step1 raw28037step0; decide +kernel
      have hl : raw28037step1Labels = raw28037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw28038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28038 raw28038Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw28038 raw28038Labels = mixedMoment B raw28038step0 raw28038step0Labels := by
      have hz : ∀ j, raw28038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28038step0 = (fun i j => raw28038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28038step0 raw28038; decide +kernel
      have hl : raw28038step0Labels = raw28038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28038 raw28038Labels permutation520 hz
    mixedMoment B raw28038step0 raw28038step0Labels = mixedMoment B raw28038step1 raw28038step1Labels := by
      have hz : ∀ j, raw28038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28038step1 = (fun i j => raw28038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28038step1 raw28038step0; decide +kernel
      have hl : raw28038step1Labels = raw28038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28038step0 raw28038step0Labels permutation80 hz
    mixedMoment B raw28038step1 raw28038step1Labels = mixedMoment B raw28038step2 raw28038step2Labels := by
      have ha : raw28038step2 = (fun i j => raw28038step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28038step2 raw28038step1; decide +kernel
      have hl : raw28038step2Labels = raw28038step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28038step1 raw28038step1Labels permutation31 permutation2
    mixedMoment B raw28038step2 raw28038step2Labels = mixedMoment B raw28038step3 raw28038step3Labels := by
      have ha : raw28038step3 = -raw28038step2 := by apply Matrix.ext; change ∀ i j, raw28038step3 i j = -(raw28038step2 i j); unfold raw28038step3 raw28038step2; decide +kernel
      have hl : raw28038step3Labels = raw28038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw28039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28039 raw28039Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw28039 raw28039Labels = mixedMoment B raw28039step0 raw28039step0Labels := by
      have hz : ∀ j, raw28039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28039step0 = (fun i j => raw28039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28039step0 raw28039; decide +kernel
      have hl : raw28039step0Labels = raw28039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28039 raw28039Labels permutation346 hz
    mixedMoment B raw28039step0 raw28039step0Labels = mixedMoment B raw28039step1 raw28039step1Labels := by
      have ha : raw28039step1 = (fun i j => raw28039step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28039step1 raw28039step0; decide +kernel
      have hl : raw28039step1Labels = raw28039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28039step0 raw28039step0Labels permutation34 permutation3
    mixedMoment B raw28039step1 raw28039step1Labels = mixedMoment B raw28039step2 raw28039step2Labels := by
      have ha : raw28039step2 = raw28039step1 := by apply Matrix.ext; unfold raw28039step2 raw28039step1; decide +kernel
      have hl : raw28039step1Labels = labelEmbedding6 ∘ raw28039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28039step1 raw28039step1Labels raw28039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw28040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28040step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28040 raw28040Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw28040 raw28040Labels = mixedMoment B raw28040step0 raw28040step0Labels := by
      have hz : ∀ j, raw28040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28040step0 = (fun i j => raw28040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28040step0 raw28040; decide +kernel
      have hl : raw28040step0Labels = raw28040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28040 raw28040Labels permutation346 hz
    mixedMoment B raw28040step0 raw28040step0Labels = mixedMoment B raw28040step1 raw28040step1Labels := by
      have ha : raw28040step1 = (fun i j => raw28040step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28040step1 raw28040step0; decide +kernel
      have hl : raw28040step1Labels = raw28040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28040step0 raw28040step0Labels permutation32 permutation3
    mixedMoment B raw28040step1 raw28040step1Labels = mixedMoment B raw28040step2 raw28040step2Labels := by
      have ha : raw28040step2 = raw28040step1 := by apply Matrix.ext; unfold raw28040step2 raw28040step1; decide +kernel
      have hl : raw28040step1Labels = labelEmbedding6 ∘ raw28040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28040step1 raw28040step1Labels raw28040step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw28041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28041 raw28041Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw28041 raw28041Labels = mixedMoment B raw28041step0 raw28041step0Labels := by
      have hz : ∀ j, raw28041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28041step0 = (fun i j => raw28041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28041step0 raw28041; decide +kernel
      have hl : raw28041step0Labels = raw28041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28041 raw28041Labels permutation346 hz
    mixedMoment B raw28041step0 raw28041step0Labels = mixedMoment B raw28041step1 raw28041step1Labels := by
      have ha : raw28041step1 = (fun i j => raw28041step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28041step1 raw28041step0; decide +kernel
      have hl : raw28041step1Labels = raw28041step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28041step0 raw28041step0Labels permutation151 permutation2
    mixedMoment B raw28041step1 raw28041step1Labels = mixedMoment B raw28041step2 raw28041step2Labels := by
      have ha : raw28041step2 = -raw28041step1 := by apply Matrix.ext; change ∀ i j, raw28041step2 i j = -(raw28041step1 i j); unfold raw28041step2 raw28041step1; decide +kernel
      have hl : raw28041step2Labels = raw28041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw28042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28042 raw28042Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw28042 raw28042Labels = mixedMoment B raw28042step0 raw28042step0Labels := by
      have ha : raw28042step0 = (fun i j => raw28042 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28042step0 raw28042; decide +kernel
      have hl : raw28042step0Labels = raw28042Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28042 raw28042Labels permutation688 permutation2
    mixedMoment B raw28042step0 raw28042step0Labels = mixedMoment B raw28042step1 raw28042step1Labels := by
      have ha : raw28042step1 = -raw28042step0 := by apply Matrix.ext; change ∀ i j, raw28042step1 i j = -(raw28042step0 i j); unfold raw28042step1 raw28042step0; decide +kernel
      have hl : raw28042step1Labels = raw28042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw28043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28043 raw28043Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw28043 raw28043Labels = mixedMoment B raw28043step0 raw28043step0Labels := by
      have hz : ∀ j, raw28043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28043step0 = (fun i j => raw28043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28043step0 raw28043; decide +kernel
      have hl : raw28043step0Labels = raw28043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28043 raw28043Labels permutation346 hz
    mixedMoment B raw28043step0 raw28043step0Labels = mixedMoment B raw28043step1 raw28043step1Labels := by
      have ha : raw28043step1 = (fun i j => raw28043step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28043step1 raw28043step0; decide +kernel
      have hl : raw28043step1Labels = raw28043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28043step0 raw28043step0Labels permutation149 permutation2
    mixedMoment B raw28043step1 raw28043step1Labels = mixedMoment B raw28043step2 raw28043step2Labels := by
      have ha : raw28043step2 = -raw28043step1 := by apply Matrix.ext; change ∀ i j, raw28043step2 i j = -(raw28043step1 i j); unfold raw28043step2 raw28043step1; decide +kernel
      have hl : raw28043step2Labels = raw28043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw28044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28044step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28044 raw28044Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw28044 raw28044Labels = mixedMoment B raw28044step0 raw28044step0Labels := by
      have hz : ∀ j, raw28044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28044step0 = (fun i j => raw28044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28044step0 raw28044; decide +kernel
      have hl : raw28044step0Labels = raw28044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28044 raw28044Labels permutation346 hz
    mixedMoment B raw28044step0 raw28044step0Labels = mixedMoment B raw28044step1 raw28044step1Labels := by
      have ha : raw28044step1 = (fun i j => raw28044step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28044step1 raw28044step0; decide +kernel
      have hl : raw28044step1Labels = raw28044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28044step0 raw28044step0Labels permutation33 permutation3
    mixedMoment B raw28044step1 raw28044step1Labels = mixedMoment B raw28044step2 raw28044step2Labels := by
      have ha : raw28044step2 = raw28044step1 := by apply Matrix.ext; unfold raw28044step2 raw28044step1; decide +kernel
      have hl : raw28044step1Labels = labelEmbedding6 ∘ raw28044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28044step1 raw28044step1Labels raw28044step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw28045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw28045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw28045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28045 raw28045Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw28045 raw28045Labels = mixedMoment B raw28045step0 raw28045step0Labels := by
      have hz : ∀ j, raw28045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28045step0 = (fun i j => raw28045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28045step0 raw28045; decide +kernel
      have hl : raw28045step0Labels = raw28045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28045 raw28045Labels permutation346 hz
    mixedMoment B raw28045step0 raw28045step0Labels = mixedMoment B raw28045step1 raw28045step1Labels := by
      have ha : raw28045step1 = (fun i j => raw28045step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28045step1 raw28045step0; decide +kernel
      have hl : raw28045step1Labels = raw28045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28045step0 raw28045step0Labels permutation151 permutation2
    mixedMoment B raw28045step1 raw28045step1Labels = mixedMoment B raw28045step2 raw28045step2Labels := by
      have ha : raw28045step2 = -raw28045step1 := by apply Matrix.ext; change ∀ i j, raw28045step2 i j = -(raw28045step1 i j); unfold raw28045step2 raw28045step1; decide +kernel
      have hl : raw28045step2Labels = raw28045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4333 node4333Labels := by rfl

def raw28046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28046 raw28046Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw28046 raw28046Labels = mixedMoment B raw28046step0 raw28046step0Labels := by
      have hz : ∀ j, raw28046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28046step0 = (fun i j => raw28046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28046step0 raw28046; decide +kernel
      have hl : raw28046step0Labels = raw28046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28046 raw28046Labels permutation346 hz
    mixedMoment B raw28046step0 raw28046step0Labels = mixedMoment B raw28046step1 raw28046step1Labels := by
      have ha : raw28046step1 = (fun i j => raw28046step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28046step1 raw28046step0; decide +kernel
      have hl : raw28046step1Labels = raw28046step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28046step0 raw28046step0Labels permutation151 permutation2
    mixedMoment B raw28046step1 raw28046step1Labels = mixedMoment B raw28046step2 raw28046step2Labels := by
      have ha : raw28046step2 = -raw28046step1 := by apply Matrix.ext; change ∀ i j, raw28046step2 i j = -(raw28046step1 i j); unfold raw28046step2 raw28046step1; decide +kernel
      have hl : raw28046step2Labels = raw28046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw28047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw28047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28047 raw28047Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw28047 raw28047Labels = mixedMoment B raw28047step0 raw28047step0Labels := by
      have ha : raw28047step0 = (fun i j => raw28047 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28047step0 raw28047; decide +kernel
      have hl : raw28047step0Labels = raw28047Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28047 raw28047Labels permutation688 permutation2
    mixedMoment B raw28047step0 raw28047step0Labels = mixedMoment B raw28047step1 raw28047step1Labels := by
      have ha : raw28047step1 = -raw28047step0 := by apply Matrix.ext; change ∀ i j, raw28047step1 i j = -(raw28047step0 i j); unfold raw28047step1 raw28047step0; decide +kernel
      have hl : raw28047step1Labels = raw28047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw28048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28048 raw28048Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw28048 raw28048Labels = mixedMoment B raw28048step0 raw28048step0Labels := by
      have hz : ∀ j, raw28048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28048step0 = (fun i j => raw28048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28048step0 raw28048; decide +kernel
      have hl : raw28048step0Labels = raw28048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28048 raw28048Labels permutation346 hz
    mixedMoment B raw28048step0 raw28048step0Labels = mixedMoment B raw28048step1 raw28048step1Labels := by
      have ha : raw28048step1 = (fun i j => raw28048step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28048step1 raw28048step0; decide +kernel
      have hl : raw28048step1Labels = raw28048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28048step0 raw28048step0Labels permutation149 permutation2
    mixedMoment B raw28048step1 raw28048step1Labels = mixedMoment B raw28048step2 raw28048step2Labels := by
      have ha : raw28048step2 = -raw28048step1 := by apply Matrix.ext; change ∀ i j, raw28048step2 i j = -(raw28048step1 i j); unfold raw28048step2 raw28048step1; decide +kernel
      have hl : raw28048step2Labels = raw28048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw28049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28049 raw28049Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw28049 raw28049Labels = mixedMoment B raw28049step0 raw28049step0Labels := by
      have hz : ∀ j, raw28049 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28049step0 = (fun i j => raw28049 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28049step0 raw28049; decide +kernel
      have hl : raw28049step0Labels = raw28049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28049 raw28049Labels permutation520 hz
    mixedMoment B raw28049step0 raw28049step0Labels = mixedMoment B raw28049step1 raw28049step1Labels := by
      have hz : ∀ j, raw28049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28049step1 = (fun i j => raw28049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28049step1 raw28049step0; decide +kernel
      have hl : raw28049step1Labels = raw28049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28049step0 raw28049step0Labels permutation80 hz
    mixedMoment B raw28049step1 raw28049step1Labels = mixedMoment B raw28049step2 raw28049step2Labels := by
      have ha : raw28049step2 = (fun i j => raw28049step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28049step2 raw28049step1; decide +kernel
      have hl : raw28049step2Labels = raw28049step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28049step1 raw28049step1Labels permutation31 permutation2
    mixedMoment B raw28049step2 raw28049step2Labels = mixedMoment B raw28049step3 raw28049step3Labels := by
      have ha : raw28049step3 = -raw28049step2 := by apply Matrix.ext; change ∀ i j, raw28049step3 i j = -(raw28049step2 i j); unfold raw28049step3 raw28049step2; decide +kernel
      have hl : raw28049step3Labels = raw28049step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw28050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw28050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28050 raw28050Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw28050 raw28050Labels = mixedMoment B raw28050step0 raw28050step0Labels := by
      have hz : ∀ j, raw28050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28050step0 = (fun i j => raw28050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28050step0 raw28050; decide +kernel
      have hl : raw28050step0Labels = raw28050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28050 raw28050Labels permutation346 hz
    mixedMoment B raw28050step0 raw28050step0Labels = mixedMoment B raw28050step1 raw28050step1Labels := by
      have ha : raw28050step1 = (fun i j => raw28050step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28050step1 raw28050step0; decide +kernel
      have hl : raw28050step1Labels = raw28050step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28050step0 raw28050step0Labels permutation150 permutation3
    mixedMoment B raw28050step1 raw28050step1Labels = mixedMoment B raw28050step2 raw28050step2Labels := by
      have ha : raw28050step2 = -raw28050step1 := by apply Matrix.ext; change ∀ i j, raw28050step2 i j = -(raw28050step1 i j); unfold raw28050step2 raw28050step1; decide +kernel
      have hl : raw28050step2Labels = raw28050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw28051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28051 raw28051Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw28051 raw28051Labels = mixedMoment B raw28051step0 raw28051step0Labels := by
      have ha : raw28051step0 = (fun i j => raw28051 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28051step0 raw28051; decide +kernel
      have hl : raw28051step0Labels = raw28051Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28051 raw28051Labels permutation686 permutation3
    mixedMoment B raw28051step0 raw28051step0Labels = mixedMoment B raw28051step1 raw28051step1Labels := by
      have ha : raw28051step1 = -raw28051step0 := by apply Matrix.ext; change ∀ i j, raw28051step1 i j = -(raw28051step0 i j); unfold raw28051step1 raw28051step0; decide +kernel
      have hl : raw28051step1Labels = raw28051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw28052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw28052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28052 raw28052Labels = mixedMoment B node3213 node3213Labels := by
  calc
    mixedMoment B raw28052 raw28052Labels = mixedMoment B raw28052step0 raw28052step0Labels := by
      have hz : ∀ j, raw28052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28052step0 = (fun i j => raw28052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28052step0 raw28052; decide +kernel
      have hl : raw28052step0Labels = raw28052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28052 raw28052Labels permutation346 hz
    mixedMoment B raw28052step0 raw28052step0Labels = mixedMoment B raw28052step1 raw28052step1Labels := by
      have ha : raw28052step1 = (fun i j => raw28052step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28052step1 raw28052step0; decide +kernel
      have hl : raw28052step1Labels = raw28052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28052step0 raw28052step0Labels permutation149 permutation3
    mixedMoment B raw28052step1 raw28052step1Labels = mixedMoment B raw28052step2 raw28052step2Labels := by
      have ha : raw28052step2 = -raw28052step1 := by apply Matrix.ext; change ∀ i j, raw28052step2 i j = -(raw28052step1 i j); unfold raw28052step2 raw28052step1; decide +kernel
      have hl : raw28052step2Labels = raw28052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3213 node3213Labels := by rfl

def raw28053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28053step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw28053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw28053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28053 raw28053Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw28053 raw28053Labels = mixedMoment B raw28053step0 raw28053step0Labels := by
      have hz : ∀ j, raw28053 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28053step0 = (fun i j => raw28053 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28053step0 raw28053; decide +kernel
      have hl : raw28053step0Labels = raw28053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28053 raw28053Labels permutation520 hz
    mixedMoment B raw28053step0 raw28053step0Labels = mixedMoment B raw28053step1 raw28053step1Labels := by
      have hz : ∀ j, raw28053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28053step1 = (fun i j => raw28053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28053step1 raw28053step0; decide +kernel
      have hl : raw28053step1Labels = raw28053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28053step0 raw28053step0Labels permutation80 hz
    mixedMoment B raw28053step1 raw28053step1Labels = mixedMoment B raw28053step2 raw28053step2Labels := by
      have ha : raw28053step2 = (fun i j => raw28053step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28053step2 raw28053step1; decide +kernel
      have hl : raw28053step2Labels = raw28053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28053step1 raw28053step1Labels permutation31 permutation3
    mixedMoment B raw28053step2 raw28053step2Labels = mixedMoment B raw28053step3 raw28053step3Labels := by
      have ha : raw28053step3 = -raw28053step2 := by apply Matrix.ext; change ∀ i j, raw28053step3 i j = -(raw28053step2 i j); unfold raw28053step3 raw28053step2; decide +kernel
      have hl : raw28053step3Labels = raw28053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw28054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw28054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28054 raw28054Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw28054 raw28054Labels = mixedMoment B raw28054step0 raw28054step0Labels := by
      have hz : ∀ j, raw28054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28054step0 = (fun i j => raw28054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28054step0 raw28054; decide +kernel
      have hl : raw28054step0Labels = raw28054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28054 raw28054Labels permutation346 hz
    mixedMoment B raw28054step0 raw28054step0Labels = mixedMoment B raw28054step1 raw28054step1Labels := by
      have ha : raw28054step1 = (fun i j => raw28054step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28054step1 raw28054step0; decide +kernel
      have hl : raw28054step1Labels = raw28054step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28054step0 raw28054step0Labels permutation146 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw28055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28055 raw28055Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw28055 raw28055Labels = mixedMoment B raw28055step0 raw28055step0Labels := by
      have hz : ∀ j, raw28055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28055step0 = (fun i j => raw28055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28055step0 raw28055; decide +kernel
      have hl : raw28055step0Labels = raw28055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28055 raw28055Labels permutation346 hz
    mixedMoment B raw28055step0 raw28055step0Labels = mixedMoment B raw28055step1 raw28055step1Labels := by
      have ha : raw28055step1 = (fun i j => raw28055step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28055step1 raw28055step0; decide +kernel
      have hl : raw28055step1Labels = raw28055step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28055step0 raw28055step0Labels permutation32 permutation3
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw28056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28056 raw28056Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw28056 raw28056Labels = mixedMoment B raw28056step0 raw28056step0Labels := by
      have ha : raw28056step0 = (fun i j => raw28056 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28056step0 raw28056; decide +kernel
      have hl : raw28056step0Labels = raw28056Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28056 raw28056Labels permutation176 permutation3
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw28057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28057 raw28057Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw28057 raw28057Labels = mixedMoment B raw28057step0 raw28057step0Labels := by
      have hz : ∀ j, raw28057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28057step0 = (fun i j => raw28057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28057step0 raw28057; decide +kernel
      have hl : raw28057step0Labels = raw28057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28057 raw28057Labels permutation346 hz
    mixedMoment B raw28057step0 raw28057step0Labels = mixedMoment B raw28057step1 raw28057step1Labels := by
      have ha : raw28057step1 = (fun i j => raw28057step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28057step1 raw28057step0; decide +kernel
      have hl : raw28057step1Labels = raw28057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28057step0 raw28057step0Labels permutation38 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw28058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw28058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28058 raw28058Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw28058 raw28058Labels = mixedMoment B raw28058step0 raw28058step0Labels := by
      have hz : ∀ j, raw28058 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28058step0 = (fun i j => raw28058 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28058step0 raw28058; decide +kernel
      have hl : raw28058step0Labels = raw28058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28058 raw28058Labels permutation520 hz
    mixedMoment B raw28058step0 raw28058step0Labels = mixedMoment B raw28058step1 raw28058step1Labels := by
      have hz : ∀ j, raw28058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28058step1 = (fun i j => raw28058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28058step1 raw28058step0; decide +kernel
      have hl : raw28058step1Labels = raw28058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28058step0 raw28058step0Labels permutation80 hz
    mixedMoment B raw28058step1 raw28058step1Labels = mixedMoment B raw28058step2 raw28058step2Labels := by
      have ha : raw28058step2 = (fun i j => raw28058step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28058step2 raw28058step1; decide +kernel
      have hl : raw28058step2Labels = raw28058step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28058step1 raw28058step1Labels permutation8 permutation3
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw28059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28059 raw28059Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw28059 raw28059Labels = mixedMoment B raw28059step0 raw28059step0Labels := by
      have hz : ∀ j, raw28059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28059step0 = (fun i j => raw28059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28059step0 raw28059; decide +kernel
      have hl : raw28059step0Labels = raw28059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28059 raw28059Labels permutation346 hz
    mixedMoment B raw28059step0 raw28059step0Labels = mixedMoment B raw28059step1 raw28059step1Labels := by
      have ha : raw28059step1 = (fun i j => raw28059step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28059step1 raw28059step0; decide +kernel
      have hl : raw28059step1Labels = raw28059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28059step0 raw28059step0Labels permutation32 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw28060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28060 raw28060Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw28060 raw28060Labels = mixedMoment B raw28060step0 raw28060step0Labels := by
      have ha : raw28060step0 = (fun i j => raw28060 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28060step0 raw28060; decide +kernel
      have hl : raw28060step0Labels = raw28060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28060 raw28060Labels permutation158 permutation3
    _ = mixedMoment B node909 node909Labels := by rfl

def raw28061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28061 raw28061Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw28061 raw28061Labels = mixedMoment B raw28061step0 raw28061step0Labels := by
      have ha : raw28061step0 = (fun i j => raw28061 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28061step0 raw28061; decide +kernel
      have hl : raw28061step0Labels = raw28061Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28061 raw28061Labels permutation158 permutation3
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw28062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28062 raw28062Labels = mixedMoment B node2528 node2528Labels := by
  calc
    mixedMoment B raw28062 raw28062Labels = mixedMoment B raw28062step0 raw28062step0Labels := by
      have ha : raw28062step0 = (fun i j => raw28062 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28062step0 raw28062; decide +kernel
      have hl : raw28062step0Labels = raw28062Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28062 raw28062Labels permutation158 permutation3
    _ = mixedMoment B node2528 node2528Labels := by rfl

def raw28063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28063 raw28063Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw28063 raw28063Labels = mixedMoment B raw28063step0 raw28063step0Labels := by
      have hz : ∀ j, raw28063 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28063step0 = (fun i j => raw28063 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28063step0 raw28063; decide +kernel
      have hl : raw28063step0Labels = raw28063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28063 raw28063Labels permutation520 hz
    mixedMoment B raw28063step0 raw28063step0Labels = mixedMoment B raw28063step1 raw28063step1Labels := by
      have ha : raw28063step1 = (fun i j => raw28063step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28063step1 raw28063step0; decide +kernel
      have hl : raw28063step1Labels = raw28063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28063step0 raw28063step0Labels permutation34 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw28064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28064 raw28064Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw28064 raw28064Labels = mixedMoment B raw28064step0 raw28064step0Labels := by
      have ha : raw28064step0 = (fun i j => raw28064 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28064step0 raw28064; decide +kernel
      have hl : raw28064step0Labels = raw28064Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28064 raw28064Labels permutation158 permutation3
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw28065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28065 raw28065Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw28065 raw28065Labels = mixedMoment B raw28065step0 raw28065step0Labels := by
      have hz : ∀ j, raw28065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28065step0 = (fun i j => raw28065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28065step0 raw28065; decide +kernel
      have hl : raw28065step0Labels = raw28065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28065 raw28065Labels permutation346 hz
    mixedMoment B raw28065step0 raw28065step0Labels = mixedMoment B raw28065step1 raw28065step1Labels := by
      have ha : raw28065step1 = (fun i j => raw28065step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28065step1 raw28065step0; decide +kernel
      have hl : raw28065step1Labels = raw28065step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28065step0 raw28065step0Labels permutation34 permutation3
    _ = mixedMoment B node931 node931Labels := by rfl

def raw28066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28066 raw28066Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw28066 raw28066Labels = mixedMoment B raw28066step0 raw28066step0Labels := by
      have hz : ∀ j, raw28066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28066step0 = (fun i j => raw28066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28066step0 raw28066; decide +kernel
      have hl : raw28066step0Labels = raw28066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28066 raw28066Labels permutation346 hz
    mixedMoment B raw28066step0 raw28066step0Labels = mixedMoment B raw28066step1 raw28066step1Labels := by
      have ha : raw28066step1 = (fun i j => raw28066step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28066step1 raw28066step0; decide +kernel
      have hl : raw28066step1Labels = raw28066step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28066step0 raw28066step0Labels permutation34 permutation3
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw28067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28067 raw28067Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw28067 raw28067Labels = mixedMoment B raw28067step0 raw28067step0Labels := by
      have ha : raw28067step0 = (fun i j => raw28067 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28067step0 raw28067; decide +kernel
      have hl : raw28067step0Labels = raw28067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28067 raw28067Labels permutation178 permutation3
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw28068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28068 raw28068Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw28068 raw28068Labels = mixedMoment B raw28068step0 raw28068step0Labels := by
      have hz : ∀ j, raw28068 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28068step0 = (fun i j => raw28068 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28068step0 raw28068; decide +kernel
      have hl : raw28068step0Labels = raw28068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28068 raw28068Labels permutation520 hz
    mixedMoment B raw28068step0 raw28068step0Labels = mixedMoment B raw28068step1 raw28068step1Labels := by
      have hz : ∀ j, raw28068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28068step1 = (fun i j => raw28068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28068step1 raw28068step0; decide +kernel
      have hl : raw28068step1Labels = raw28068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28068step0 raw28068step0Labels permutation80 hz
    mixedMoment B raw28068step1 raw28068step1Labels = mixedMoment B raw28068step2 raw28068step2Labels := by
      have ha : raw28068step2 = (fun i j => raw28068step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28068step2 raw28068step1; decide +kernel
      have hl : raw28068step2Labels = raw28068step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28068step1 raw28068step1Labels permutation8 permutation3
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw28069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28069 raw28069Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw28069 raw28069Labels = mixedMoment B raw28069step0 raw28069step0Labels := by
      have hz : ∀ j, raw28069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28069step0 = (fun i j => raw28069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28069step0 raw28069; decide +kernel
      have hl : raw28069step0Labels = raw28069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28069 raw28069Labels permutation346 hz
    mixedMoment B raw28069step0 raw28069step0Labels = mixedMoment B raw28069step1 raw28069step1Labels := by
      have ha : raw28069step1 = (fun i j => raw28069step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28069step1 raw28069step0; decide +kernel
      have hl : raw28069step1Labels = raw28069step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28069step0 raw28069step0Labels permutation34 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw28070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28070 raw28070Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw28070 raw28070Labels = mixedMoment B raw28070step0 raw28070step0Labels := by
      have hz : ∀ j, raw28070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28070step0 = (fun i j => raw28070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28070step0 raw28070; decide +kernel
      have hl : raw28070step0Labels = raw28070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28070 raw28070Labels permutation346 hz
    mixedMoment B raw28070step0 raw28070step0Labels = mixedMoment B raw28070step1 raw28070step1Labels := by
      have ha : raw28070step1 = (fun i j => raw28070step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28070step1 raw28070step0; decide +kernel
      have hl : raw28070step1Labels = raw28070step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28070step0 raw28070step0Labels permutation32 permutation3
    _ = mixedMoment B node914 node914Labels := by rfl

def raw28071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28071 raw28071Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw28071 raw28071Labels = mixedMoment B raw28071step0 raw28071step0Labels := by
      have hz : ∀ j, raw28071 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28071step0 = (fun i j => raw28071 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28071step0 raw28071; decide +kernel
      have hl : raw28071step0Labels = raw28071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28071 raw28071Labels permutation346 hz
    mixedMoment B raw28071step0 raw28071step0Labels = mixedMoment B raw28071step1 raw28071step1Labels := by
      have ha : raw28071step1 = (fun i j => raw28071step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28071step1 raw28071step0; decide +kernel
      have hl : raw28071step1Labels = raw28071step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28071step0 raw28071step0Labels permutation32 permutation3
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw28072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw28072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28072 raw28072Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw28072 raw28072Labels = mixedMoment B raw28072step0 raw28072step0Labels := by
      have ha : raw28072step0 = (fun i j => raw28072 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28072step0 raw28072; decide +kernel
      have hl : raw28072step0Labels = raw28072Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28072 raw28072Labels permutation176 permutation3
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw28073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw28073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28073 raw28073Labels = mixedMoment B node2532 node2532Labels := by
  calc
    mixedMoment B raw28073 raw28073Labels = mixedMoment B raw28073step0 raw28073step0Labels := by
      have hz : ∀ j, raw28073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28073step0 = (fun i j => raw28073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28073step0 raw28073; decide +kernel
      have hl : raw28073step0Labels = raw28073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28073 raw28073Labels permutation346 hz
    mixedMoment B raw28073step0 raw28073step0Labels = mixedMoment B raw28073step1 raw28073step1Labels := by
      have ha : raw28073step1 = (fun i j => raw28073step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28073step1 raw28073step0; decide +kernel
      have hl : raw28073step1Labels = raw28073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28073step0 raw28073step0Labels permutation32 permutation3
    _ = mixedMoment B node2532 node2532Labels := by rfl

def raw28074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28074 raw28074Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw28074 raw28074Labels = mixedMoment B raw28074step0 raw28074step0Labels := by
      have hz : ∀ j, raw28074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28074step0 = (fun i j => raw28074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28074step0 raw28074; decide +kernel
      have hl : raw28074step0Labels = raw28074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28074 raw28074Labels permutation346 hz
    mixedMoment B raw28074step0 raw28074step0Labels = mixedMoment B raw28074step1 raw28074step1Labels := by
      have ha : raw28074step1 = (fun i j => raw28074step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28074step1 raw28074step0; decide +kernel
      have hl : raw28074step1Labels = raw28074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28074step0 raw28074step0Labels permutation33 permutation3
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw28075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw28075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28075 raw28075Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw28075 raw28075Labels = mixedMoment B raw28075step0 raw28075step0Labels := by
      have hz : ∀ j, raw28075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28075step0 = (fun i j => raw28075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28075step0 raw28075; decide +kernel
      have hl : raw28075step0Labels = raw28075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28075 raw28075Labels permutation346 hz
    mixedMoment B raw28075step0 raw28075step0Labels = mixedMoment B raw28075step1 raw28075step1Labels := by
      have ha : raw28075step1 = (fun i j => raw28075step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28075step1 raw28075step0; decide +kernel
      have hl : raw28075step1Labels = raw28075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28075step0 raw28075step0Labels permutation32 permutation3
    _ = mixedMoment B node911 node911Labels := by rfl

def raw28076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28076 raw28076Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw28076 raw28076Labels = mixedMoment B raw28076step0 raw28076step0Labels := by
      have hz : ∀ j, raw28076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28076step0 = (fun i j => raw28076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28076step0 raw28076; decide +kernel
      have hl : raw28076step0Labels = raw28076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28076 raw28076Labels permutation346 hz
    mixedMoment B raw28076step0 raw28076step0Labels = mixedMoment B raw28076step1 raw28076step1Labels := by
      have ha : raw28076step1 = (fun i j => raw28076step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28076step1 raw28076step0; decide +kernel
      have hl : raw28076step1Labels = raw28076step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28076step0 raw28076step0Labels permutation151 permutation3
    mixedMoment B raw28076step1 raw28076step1Labels = mixedMoment B raw28076step2 raw28076step2Labels := by
      have ha : raw28076step2 = -raw28076step1 := by apply Matrix.ext; change ∀ i j, raw28076step2 i j = -(raw28076step1 i j); unfold raw28076step2 raw28076step1; decide +kernel
      have hl : raw28076step2Labels = raw28076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw28077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28077 raw28077Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw28077 raw28077Labels = mixedMoment B raw28077step0 raw28077step0Labels := by
      have ha : raw28077step0 = (fun i j => raw28077 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28077step0 raw28077; decide +kernel
      have hl : raw28077step0Labels = raw28077Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28077 raw28077Labels permutation686 permutation3
    mixedMoment B raw28077step0 raw28077step0Labels = mixedMoment B raw28077step1 raw28077step1Labels := by
      have ha : raw28077step1 = -raw28077step0 := by apply Matrix.ext; change ∀ i j, raw28077step1 i j = -(raw28077step0 i j); unfold raw28077step1 raw28077step0; decide +kernel
      have hl : raw28077step1Labels = raw28077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw28078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28078 raw28078Labels = mixedMoment B node1340 node1340Labels := by
  calc
    mixedMoment B raw28078 raw28078Labels = mixedMoment B raw28078step0 raw28078step0Labels := by
      have hz : ∀ j, raw28078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28078step0 = (fun i j => raw28078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28078step0 raw28078; decide +kernel
      have hl : raw28078step0Labels = raw28078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28078 raw28078Labels permutation346 hz
    mixedMoment B raw28078step0 raw28078step0Labels = mixedMoment B raw28078step1 raw28078step1Labels := by
      have ha : raw28078step1 = (fun i j => raw28078step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28078step1 raw28078step0; decide +kernel
      have hl : raw28078step1Labels = raw28078step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28078step0 raw28078step0Labels permutation149 permutation3
    mixedMoment B raw28078step1 raw28078step1Labels = mixedMoment B raw28078step2 raw28078step2Labels := by
      have ha : raw28078step2 = -raw28078step1 := by apply Matrix.ext; change ∀ i j, raw28078step2 i j = -(raw28078step1 i j); unfold raw28078step2 raw28078step1; decide +kernel
      have hl : raw28078step2Labels = raw28078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1340 node1340Labels := by rfl

def raw28079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw28079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28079 raw28079Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw28079 raw28079Labels = mixedMoment B raw28079step0 raw28079step0Labels := by
      have hz : ∀ j, raw28079 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28079step0 = (fun i j => raw28079 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28079step0 raw28079; decide +kernel
      have hl : raw28079step0Labels = raw28079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28079 raw28079Labels permutation520 hz
    mixedMoment B raw28079step0 raw28079step0Labels = mixedMoment B raw28079step1 raw28079step1Labels := by
      have hz : ∀ j, raw28079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28079step1 = (fun i j => raw28079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28079step1 raw28079step0; decide +kernel
      have hl : raw28079step1Labels = raw28079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28079step0 raw28079step0Labels permutation80 hz
    mixedMoment B raw28079step1 raw28079step1Labels = mixedMoment B raw28079step2 raw28079step2Labels := by
      have ha : raw28079step2 = (fun i j => raw28079step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28079step2 raw28079step1; decide +kernel
      have hl : raw28079step2Labels = raw28079step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28079step1 raw28079step1Labels permutation31 permutation3
    mixedMoment B raw28079step2 raw28079step2Labels = mixedMoment B raw28079step3 raw28079step3Labels := by
      have ha : raw28079step3 = -raw28079step2 := by apply Matrix.ext; change ∀ i j, raw28079step3 i j = -(raw28079step2 i j); unfold raw28079step3 raw28079step2; decide +kernel
      have hl : raw28079step3Labels = raw28079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw28080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw28080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw28080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28080 raw28080Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw28080 raw28080Labels = mixedMoment B raw28080step0 raw28080step0Labels := by
      have hz : ∀ j, raw28080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28080step0 = (fun i j => raw28080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28080step0 raw28080; decide +kernel
      have hl : raw28080step0Labels = raw28080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28080 raw28080Labels permutation346 hz
    mixedMoment B raw28080step0 raw28080step0Labels = mixedMoment B raw28080step1 raw28080step1Labels := by
      have ha : raw28080step1 = (fun i j => raw28080step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28080step1 raw28080step0; decide +kernel
      have hl : raw28080step1Labels = raw28080step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28080step0 raw28080step0Labels permutation150 permutation7
    mixedMoment B raw28080step1 raw28080step1Labels = mixedMoment B raw28080step2 raw28080step2Labels := by
      have ha : raw28080step2 = raw28080step1 := by apply Matrix.ext; unfold raw28080step2 raw28080step1; decide +kernel
      have hl : raw28080step1Labels = labelEmbedding1 ∘ raw28080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28080step1 raw28080step1Labels raw28080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw28081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28081 raw28081Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw28081 raw28081Labels = mixedMoment B raw28081step0 raw28081step0Labels := by
      have ha : raw28081step0 = (fun i j => raw28081 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28081step0 raw28081; decide +kernel
      have hl : raw28081step0Labels = raw28081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28081 raw28081Labels permutation682 permutation7
    mixedMoment B raw28081step0 raw28081step0Labels = mixedMoment B raw28081step1 raw28081step1Labels := by
      have ha : raw28081step1 = raw28081step0 := by apply Matrix.ext; unfold raw28081step1 raw28081step0; decide +kernel
      have hl : raw28081step0Labels = labelEmbedding1 ∘ raw28081step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28081step0 raw28081step0Labels raw28081step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw28082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw28082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw28082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28082 raw28082Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw28082 raw28082Labels = mixedMoment B raw28082step0 raw28082step0Labels := by
      have hz : ∀ j, raw28082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28082step0 = (fun i j => raw28082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28082step0 raw28082; decide +kernel
      have hl : raw28082step0Labels = raw28082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28082 raw28082Labels permutation346 hz
    mixedMoment B raw28082step0 raw28082step0Labels = mixedMoment B raw28082step1 raw28082step1Labels := by
      have ha : raw28082step1 = (fun i j => raw28082step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28082step1 raw28082step0; decide +kernel
      have hl : raw28082step1Labels = raw28082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28082step0 raw28082step0Labels permutation149 permutation7
    mixedMoment B raw28082step1 raw28082step1Labels = mixedMoment B raw28082step2 raw28082step2Labels := by
      have ha : raw28082step2 = raw28082step1 := by apply Matrix.ext; unfold raw28082step2 raw28082step1; decide +kernel
      have hl : raw28082step1Labels = labelEmbedding1 ∘ raw28082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28082step1 raw28082step1Labels raw28082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw28083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28083step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28083 raw28083Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw28083 raw28083Labels = mixedMoment B raw28083step0 raw28083step0Labels := by
      have hz : ∀ j, raw28083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28083step0 = (fun i j => raw28083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28083step0 raw28083; decide +kernel
      have hl : raw28083step0Labels = raw28083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28083 raw28083Labels permutation520 hz
    mixedMoment B raw28083step0 raw28083step0Labels = mixedMoment B raw28083step1 raw28083step1Labels := by
      have hz : ∀ j, raw28083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28083step1 = (fun i j => raw28083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28083step1 raw28083step0; decide +kernel
      have hl : raw28083step1Labels = raw28083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28083step0 raw28083step0Labels permutation80 hz
    mixedMoment B raw28083step1 raw28083step1Labels = mixedMoment B raw28083step2 raw28083step2Labels := by
      have ha : raw28083step2 = (fun i j => raw28083step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28083step2 raw28083step1; decide +kernel
      have hl : raw28083step2Labels = raw28083step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28083step1 raw28083step1Labels permutation31 permutation7
    mixedMoment B raw28083step2 raw28083step2Labels = mixedMoment B raw28083step3 raw28083step3Labels := by
      have ha : raw28083step3 = raw28083step2 := by apply Matrix.ext; unfold raw28083step3 raw28083step2; decide +kernel
      have hl : raw28083step2Labels = labelEmbedding1 ∘ raw28083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28083step2 raw28083step2Labels raw28083step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw28084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28084 raw28084Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw28084 raw28084Labels = mixedMoment B raw28084step0 raw28084step0Labels := by
      have hz : ∀ j, raw28084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28084step0 = (fun i j => raw28084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28084step0 raw28084; decide +kernel
      have hl : raw28084step0Labels = raw28084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28084 raw28084Labels permutation346 hz
    mixedMoment B raw28084step0 raw28084step0Labels = mixedMoment B raw28084step1 raw28084step1Labels := by
      have ha : raw28084step1 = (fun i j => raw28084step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28084step1 raw28084step0; decide +kernel
      have hl : raw28084step1Labels = raw28084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28084step0 raw28084step0Labels permutation151 permutation7
    mixedMoment B raw28084step1 raw28084step1Labels = mixedMoment B raw28084step2 raw28084step2Labels := by
      have ha : raw28084step2 = raw28084step1 := by apply Matrix.ext; unfold raw28084step2 raw28084step1; decide +kernel
      have hl : raw28084step1Labels = labelEmbedding1 ∘ raw28084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28084step1 raw28084step1Labels raw28084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw28085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28085step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw28085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw28085step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28085step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw28085step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28085 raw28085Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw28085 raw28085Labels = mixedMoment B raw28085step0 raw28085step0Labels := by
      have hz : ∀ j, raw28085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28085step0 = (fun i j => raw28085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28085step0 raw28085; decide +kernel
      have hl : raw28085step0Labels = raw28085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28085 raw28085Labels permutation346 hz
    mixedMoment B raw28085step0 raw28085step0Labels = mixedMoment B raw28085step1 raw28085step1Labels := by
      have ha : raw28085step1 = (fun i j => raw28085step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28085step1 raw28085step0; decide +kernel
      have hl : raw28085step1Labels = raw28085step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28085step0 raw28085step0Labels permutation50 permutation5
    mixedMoment B raw28085step1 raw28085step1Labels = mixedMoment B raw28085step2 raw28085step2Labels := by
      have ha : raw28085step2 = -raw28085step1 := by apply Matrix.ext; change ∀ i j, raw28085step2 i j = -(raw28085step1 i j); unfold raw28085step2 raw28085step1; decide +kernel
      have hl : raw28085step2Labels = raw28085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28085step2 raw28085step2Labels = mixedMoment B raw28085step3 raw28085step3Labels := by
      have ha : raw28085step3 = raw28085step2 := by apply Matrix.ext; unfold raw28085step3 raw28085step2; decide +kernel
      have hl : raw28085step2Labels = labelEmbedding1 ∘ raw28085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28085step2 raw28085step2Labels raw28085step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw28086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28086 raw28086Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw28086 raw28086Labels = mixedMoment B raw28086step0 raw28086step0Labels := by
      have ha : raw28086step0 = (fun i j => raw28086 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28086step0 raw28086; decide +kernel
      have hl : raw28086step0Labels = raw28086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28086 raw28086Labels permutation680 permutation7
    mixedMoment B raw28086step0 raw28086step0Labels = mixedMoment B raw28086step1 raw28086step1Labels := by
      have ha : raw28086step1 = raw28086step0 := by apply Matrix.ext; unfold raw28086step1 raw28086step0; decide +kernel
      have hl : raw28086step0Labels = labelEmbedding1 ∘ raw28086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28086step0 raw28086step0Labels raw28086step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw28087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28087 raw28087Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw28087 raw28087Labels = mixedMoment B raw28087step0 raw28087step0Labels := by
      have hz : ∀ j, raw28087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28087step0 = (fun i j => raw28087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28087step0 raw28087; decide +kernel
      have hl : raw28087step0Labels = raw28087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28087 raw28087Labels permutation346 hz
    mixedMoment B raw28087step0 raw28087step0Labels = mixedMoment B raw28087step1 raw28087step1Labels := by
      have ha : raw28087step1 = (fun i j => raw28087step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28087step1 raw28087step0; decide +kernel
      have hl : raw28087step1Labels = raw28087step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28087step0 raw28087step0Labels permutation149 permutation7
    mixedMoment B raw28087step1 raw28087step1Labels = mixedMoment B raw28087step2 raw28087step2Labels := by
      have ha : raw28087step2 = raw28087step1 := by apply Matrix.ext; unfold raw28087step2 raw28087step1; decide +kernel
      have hl : raw28087step1Labels = labelEmbedding1 ∘ raw28087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28087step1 raw28087step1Labels raw28087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw28088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw28088step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28088 raw28088Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw28088 raw28088Labels = mixedMoment B raw28088step0 raw28088step0Labels := by
      have hz : ∀ j, raw28088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28088step0 = (fun i j => raw28088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28088step0 raw28088; decide +kernel
      have hl : raw28088step0Labels = raw28088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28088 raw28088Labels permutation520 hz
    mixedMoment B raw28088step0 raw28088step0Labels = mixedMoment B raw28088step1 raw28088step1Labels := by
      have hz : ∀ j, raw28088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28088step1 = (fun i j => raw28088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28088step1 raw28088step0; decide +kernel
      have hl : raw28088step1Labels = raw28088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28088step0 raw28088step0Labels permutation80 hz
    mixedMoment B raw28088step1 raw28088step1Labels = mixedMoment B raw28088step2 raw28088step2Labels := by
      have ha : raw28088step2 = (fun i j => raw28088step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28088step2 raw28088step1; decide +kernel
      have hl : raw28088step2Labels = raw28088step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28088step1 raw28088step1Labels permutation29 permutation7
    mixedMoment B raw28088step2 raw28088step2Labels = mixedMoment B raw28088step3 raw28088step3Labels := by
      have ha : raw28088step3 = raw28088step2 := by apply Matrix.ext; unfold raw28088step3 raw28088step2; decide +kernel
      have hl : raw28088step2Labels = labelEmbedding1 ∘ raw28088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28088step2 raw28088step2Labels raw28088step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw28089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw28089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28089 raw28089Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw28089 raw28089Labels = mixedMoment B raw28089step0 raw28089step0Labels := by
      have hz : ∀ j, raw28089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28089step0 = (fun i j => raw28089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28089step0 raw28089; decide +kernel
      have hl : raw28089step0Labels = raw28089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28089 raw28089Labels permutation346 hz
    mixedMoment B raw28089step0 raw28089step0Labels = mixedMoment B raw28089step1 raw28089step1Labels := by
      have ha : raw28089step1 = (fun i j => raw28089step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28089step1 raw28089step0; decide +kernel
      have hl : raw28089step1Labels = raw28089step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28089step0 raw28089step0Labels permutation149 permutation7
    mixedMoment B raw28089step1 raw28089step1Labels = mixedMoment B raw28089step2 raw28089step2Labels := by
      have ha : raw28089step2 = raw28089step1 := by apply Matrix.ext; unfold raw28089step2 raw28089step1; decide +kernel
      have hl : raw28089step1Labels = labelEmbedding1 ∘ raw28089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28089step1 raw28089step1Labels raw28089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw28090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw28090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw28090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw28090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28090 raw28090Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw28090 raw28090Labels = mixedMoment B raw28090step0 raw28090step0Labels := by
      have ha : raw28090step0 = (fun i j => raw28090 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28090step0 raw28090; decide +kernel
      have hl : raw28090step0Labels = raw28090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28090 raw28090Labels permutation172 permutation5
    mixedMoment B raw28090step0 raw28090step0Labels = mixedMoment B raw28090step1 raw28090step1Labels := by
      have ha : raw28090step1 = -raw28090step0 := by apply Matrix.ext; change ∀ i j, raw28090step1 i j = -(raw28090step0 i j); unfold raw28090step1 raw28090step0; decide +kernel
      have hl : raw28090step1Labels = raw28090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28090step1 raw28090step1Labels = mixedMoment B raw28090step2 raw28090step2Labels := by
      have ha : raw28090step2 = raw28090step1 := by apply Matrix.ext; unfold raw28090step2 raw28090step1; decide +kernel
      have hl : raw28090step1Labels = labelEmbedding1 ∘ raw28090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28090step1 raw28090step1Labels raw28090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw28091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28091 raw28091Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw28091 raw28091Labels = mixedMoment B raw28091step0 raw28091step0Labels := by
      have ha : raw28091step0 = (fun i j => raw28091 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28091step0 raw28091; decide +kernel
      have hl : raw28091step0Labels = raw28091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28091 raw28091Labels permutation646 permutation7
    mixedMoment B raw28091step0 raw28091step0Labels = mixedMoment B raw28091step1 raw28091step1Labels := by
      have ha : raw28091step1 = raw28091step0 := by apply Matrix.ext; unfold raw28091step1 raw28091step0; decide +kernel
      have hl : raw28091step0Labels = labelEmbedding1 ∘ raw28091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28091step0 raw28091step0Labels raw28091step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw28092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28092 raw28092Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw28092 raw28092Labels = mixedMoment B raw28092step0 raw28092step0Labels := by
      have ha : raw28092step0 = (fun i j => raw28092 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28092step0 raw28092; decide +kernel
      have hl : raw28092step0Labels = raw28092Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28092 raw28092Labels permutation644 permutation7
    mixedMoment B raw28092step0 raw28092step0Labels = mixedMoment B raw28092step1 raw28092step1Labels := by
      have ha : raw28092step1 = raw28092step0 := by apply Matrix.ext; unfold raw28092step1 raw28092step0; decide +kernel
      have hl : raw28092step0Labels = labelEmbedding1 ∘ raw28092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28092step0 raw28092step0Labels raw28092step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

def raw28093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28093 raw28093Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw28093 raw28093Labels = mixedMoment B raw28093step0 raw28093step0Labels := by
      have hz : ∀ j, raw28093 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28093step0 = (fun i j => raw28093 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28093step0 raw28093; decide +kernel
      have hl : raw28093step0Labels = raw28093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28093 raw28093Labels permutation520 hz
    mixedMoment B raw28093step0 raw28093step0Labels = mixedMoment B raw28093step1 raw28093step1Labels := by
      have ha : raw28093step1 = (fun i j => raw28093step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28093step1 raw28093step0; decide +kernel
      have hl : raw28093step1Labels = raw28093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28093step0 raw28093step0Labels permutation145 permutation7
    mixedMoment B raw28093step1 raw28093step1Labels = mixedMoment B raw28093step2 raw28093step2Labels := by
      have ha : raw28093step2 = raw28093step1 := by apply Matrix.ext; unfold raw28093step2 raw28093step1; decide +kernel
      have hl : raw28093step1Labels = labelEmbedding1 ∘ raw28093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28093step1 raw28093step1Labels raw28093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw28094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28094 raw28094Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw28094 raw28094Labels = mixedMoment B raw28094step0 raw28094step0Labels := by
      have ha : raw28094step0 = (fun i j => raw28094 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28094step0 raw28094; decide +kernel
      have hl : raw28094step0Labels = raw28094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28094 raw28094Labels permutation646 permutation7
    mixedMoment B raw28094step0 raw28094step0Labels = mixedMoment B raw28094step1 raw28094step1Labels := by
      have ha : raw28094step1 = raw28094step0 := by apply Matrix.ext; unfold raw28094step1 raw28094step0; decide +kernel
      have hl : raw28094step0Labels = labelEmbedding1 ∘ raw28094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28094step0 raw28094step0Labels raw28094step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw28095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw28095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw28095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28095step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw28095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28095 raw28095Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw28095 raw28095Labels = mixedMoment B raw28095step0 raw28095step0Labels := by
      have hz : ∀ j, raw28095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28095step0 = (fun i j => raw28095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28095step0 raw28095; decide +kernel
      have hl : raw28095step0Labels = raw28095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28095 raw28095Labels permutation346 hz
    mixedMoment B raw28095step0 raw28095step0Labels = mixedMoment B raw28095step1 raw28095step1Labels := by
      have ha : raw28095step1 = (fun i j => raw28095step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28095step1 raw28095step0; decide +kernel
      have hl : raw28095step1Labels = raw28095step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28095step0 raw28095step0Labels permutation37 permutation5
    mixedMoment B raw28095step1 raw28095step1Labels = mixedMoment B raw28095step2 raw28095step2Labels := by
      have ha : raw28095step2 = -raw28095step1 := by apply Matrix.ext; change ∀ i j, raw28095step2 i j = -(raw28095step1 i j); unfold raw28095step2 raw28095step1; decide +kernel
      have hl : raw28095step2Labels = raw28095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28095step2 raw28095step2Labels = mixedMoment B raw28095step3 raw28095step3Labels := by
      have ha : raw28095step3 = raw28095step2 := by apply Matrix.ext; unfold raw28095step3 raw28095step2; decide +kernel
      have hl : raw28095step2Labels = labelEmbedding1 ∘ raw28095step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28095step2 raw28095step2Labels raw28095step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

def raw28096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw28096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28096 raw28096Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw28096 raw28096Labels = mixedMoment B raw28096step0 raw28096step0Labels := by
      have hz : ∀ j, raw28096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28096step0 = (fun i j => raw28096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28096step0 raw28096; decide +kernel
      have hl : raw28096step0Labels = raw28096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28096 raw28096Labels permutation346 hz
    mixedMoment B raw28096step0 raw28096step0Labels = mixedMoment B raw28096step1 raw28096step1Labels := by
      have ha : raw28096step1 = (fun i j => raw28096step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28096step1 raw28096step0; decide +kernel
      have hl : raw28096step1Labels = raw28096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28096step0 raw28096step0Labels permutation151 permutation7
    mixedMoment B raw28096step1 raw28096step1Labels = mixedMoment B raw28096step2 raw28096step2Labels := by
      have ha : raw28096step2 = raw28096step1 := by apply Matrix.ext; unfold raw28096step2 raw28096step1; decide +kernel
      have hl : raw28096step1Labels = labelEmbedding1 ∘ raw28096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28096step1 raw28096step1Labels raw28096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw28097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28097 raw28097Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw28097 raw28097Labels = mixedMoment B raw28097step0 raw28097step0Labels := by
      have ha : raw28097step0 = (fun i j => raw28097 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28097step0 raw28097; decide +kernel
      have hl : raw28097step0Labels = raw28097Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28097 raw28097Labels permutation682 permutation7
    mixedMoment B raw28097step0 raw28097step0Labels = mixedMoment B raw28097step1 raw28097step1Labels := by
      have ha : raw28097step1 = raw28097step0 := by apply Matrix.ext; unfold raw28097step1 raw28097step0; decide +kernel
      have hl : raw28097step0Labels = labelEmbedding1 ∘ raw28097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28097step0 raw28097step0Labels raw28097step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw28098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw28098step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28098step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28098 raw28098Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw28098 raw28098Labels = mixedMoment B raw28098step0 raw28098step0Labels := by
      have hz : ∀ j, raw28098 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28098step0 = (fun i j => raw28098 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28098step0 raw28098; decide +kernel
      have hl : raw28098step0Labels = raw28098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28098 raw28098Labels permutation520 hz
    mixedMoment B raw28098step0 raw28098step0Labels = mixedMoment B raw28098step1 raw28098step1Labels := by
      have hz : ∀ j, raw28098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28098step1 = (fun i j => raw28098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28098step1 raw28098step0; decide +kernel
      have hl : raw28098step1Labels = raw28098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28098step0 raw28098step0Labels permutation80 hz
    mixedMoment B raw28098step1 raw28098step1Labels = mixedMoment B raw28098step2 raw28098step2Labels := by
      have ha : raw28098step2 = (fun i j => raw28098step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28098step2 raw28098step1; decide +kernel
      have hl : raw28098step2Labels = raw28098step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28098step1 raw28098step1Labels permutation31 permutation7
    mixedMoment B raw28098step2 raw28098step2Labels = mixedMoment B raw28098step3 raw28098step3Labels := by
      have ha : raw28098step3 = raw28098step2 := by apply Matrix.ext; unfold raw28098step3 raw28098step2; decide +kernel
      have hl : raw28098step2Labels = labelEmbedding1 ∘ raw28098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28098step2 raw28098step2Labels raw28098step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw28099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw28099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28099 raw28099Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw28099 raw28099Labels = mixedMoment B raw28099step0 raw28099step0Labels := by
      have hz : ∀ j, raw28099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28099step0 = (fun i j => raw28099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28099step0 raw28099; decide +kernel
      have hl : raw28099step0Labels = raw28099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28099 raw28099Labels permutation346 hz
    mixedMoment B raw28099step0 raw28099step0Labels = mixedMoment B raw28099step1 raw28099step1Labels := by
      have ha : raw28099step1 = (fun i j => raw28099step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28099step1 raw28099step0; decide +kernel
      have hl : raw28099step1Labels = raw28099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28099step0 raw28099step0Labels permutation151 permutation7
    mixedMoment B raw28099step1 raw28099step1Labels = mixedMoment B raw28099step2 raw28099step2Labels := by
      have ha : raw28099step2 = raw28099step1 := by apply Matrix.ext; unfold raw28099step2 raw28099step1; decide +kernel
      have hl : raw28099step1Labels = labelEmbedding1 ∘ raw28099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28099step1 raw28099step1Labels raw28099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw28100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw28100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw28100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw28100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28100 raw28100Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw28100 raw28100Labels = mixedMoment B raw28100step0 raw28100step0Labels := by
      have hz : ∀ j, raw28100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28100step0 = (fun i j => raw28100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28100step0 raw28100; decide +kernel
      have hl : raw28100step0Labels = raw28100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28100 raw28100Labels permutation346 hz
    mixedMoment B raw28100step0 raw28100step0Labels = mixedMoment B raw28100step1 raw28100step1Labels := by
      have ha : raw28100step1 = (fun i j => raw28100step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28100step1 raw28100step0; decide +kernel
      have hl : raw28100step1Labels = raw28100step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28100step0 raw28100step0Labels permutation36 permutation5
    mixedMoment B raw28100step1 raw28100step1Labels = mixedMoment B raw28100step2 raw28100step2Labels := by
      have ha : raw28100step2 = -raw28100step1 := by apply Matrix.ext; change ∀ i j, raw28100step2 i j = -(raw28100step1 i j); unfold raw28100step2 raw28100step1; decide +kernel
      have hl : raw28100step2Labels = raw28100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28100step2 raw28100step2Labels = mixedMoment B raw28100step3 raw28100step3Labels := by
      have ha : raw28100step3 = raw28100step2 := by apply Matrix.ext; unfold raw28100step3 raw28100step2; decide +kernel
      have hl : raw28100step2Labels = labelEmbedding1 ∘ raw28100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28100step2 raw28100step2Labels raw28100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw28101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28101 raw28101Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw28101 raw28101Labels = mixedMoment B raw28101step0 raw28101step0Labels := by
      have hz : ∀ j, raw28101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28101step0 = (fun i j => raw28101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28101step0 raw28101; decide +kernel
      have hl : raw28101step0Labels = raw28101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28101 raw28101Labels permutation346 hz
    mixedMoment B raw28101step0 raw28101step0Labels = mixedMoment B raw28101step1 raw28101step1Labels := by
      have ha : raw28101step1 = (fun i j => raw28101step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28101step1 raw28101step0; decide +kernel
      have hl : raw28101step1Labels = raw28101step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28101step0 raw28101step0Labels permutation151 permutation7
    mixedMoment B raw28101step1 raw28101step1Labels = mixedMoment B raw28101step2 raw28101step2Labels := by
      have ha : raw28101step2 = raw28101step1 := by apply Matrix.ext; unfold raw28101step2 raw28101step1; decide +kernel
      have hl : raw28101step1Labels = labelEmbedding1 ∘ raw28101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28101step1 raw28101step1Labels raw28101step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw28102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28102 raw28102Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw28102 raw28102Labels = mixedMoment B raw28102step0 raw28102step0Labels := by
      have ha : raw28102step0 = (fun i j => raw28102 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28102step0 raw28102; decide +kernel
      have hl : raw28102step0Labels = raw28102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28102 raw28102Labels permutation682 permutation7
    mixedMoment B raw28102step0 raw28102step0Labels = mixedMoment B raw28102step1 raw28102step1Labels := by
      have ha : raw28102step1 = raw28102step0 := by apply Matrix.ext; unfold raw28102step1 raw28102step0; decide +kernel
      have hl : raw28102step0Labels = labelEmbedding1 ∘ raw28102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28102step0 raw28102step0Labels raw28102step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw28103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28103 raw28103Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw28103 raw28103Labels = mixedMoment B raw28103step0 raw28103step0Labels := by
      have hz : ∀ j, raw28103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28103step0 = (fun i j => raw28103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28103step0 raw28103; decide +kernel
      have hl : raw28103step0Labels = raw28103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28103 raw28103Labels permutation346 hz
    mixedMoment B raw28103step0 raw28103step0Labels = mixedMoment B raw28103step1 raw28103step1Labels := by
      have ha : raw28103step1 = (fun i j => raw28103step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28103step1 raw28103step0; decide +kernel
      have hl : raw28103step1Labels = raw28103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28103step0 raw28103step0Labels permutation149 permutation7
    mixedMoment B raw28103step1 raw28103step1Labels = mixedMoment B raw28103step2 raw28103step2Labels := by
      have ha : raw28103step2 = raw28103step1 := by apply Matrix.ext; unfold raw28103step2 raw28103step1; decide +kernel
      have hl : raw28103step1Labels = labelEmbedding1 ∘ raw28103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28103step1 raw28103step1Labels raw28103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

def raw28104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw28104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28104 raw28104Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw28104 raw28104Labels = mixedMoment B raw28104step0 raw28104step0Labels := by
      have hz : ∀ j, raw28104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28104step0 = (fun i j => raw28104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28104step0 raw28104; decide +kernel
      have hl : raw28104step0Labels = raw28104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28104 raw28104Labels permutation346 hz
    mixedMoment B raw28104step0 raw28104step0Labels = mixedMoment B raw28104step1 raw28104step1Labels := by
      have ha : raw28104step1 = (fun i j => raw28104step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28104step1 raw28104step0; decide +kernel
      have hl : raw28104step1Labels = raw28104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28104step0 raw28104step0Labels permutation151 permutation7
    mixedMoment B raw28104step1 raw28104step1Labels = mixedMoment B raw28104step2 raw28104step2Labels := by
      have ha : raw28104step2 = raw28104step1 := by apply Matrix.ext; unfold raw28104step2 raw28104step1; decide +kernel
      have hl : raw28104step1Labels = labelEmbedding1 ∘ raw28104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28104step1 raw28104step1Labels raw28104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw28105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw28105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw28105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28105step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw28105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28105 raw28105Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw28105 raw28105Labels = mixedMoment B raw28105step0 raw28105step0Labels := by
      have hz : ∀ j, raw28105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28105step0 = (fun i j => raw28105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28105step0 raw28105; decide +kernel
      have hl : raw28105step0Labels = raw28105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28105 raw28105Labels permutation346 hz
    mixedMoment B raw28105step0 raw28105step0Labels = mixedMoment B raw28105step1 raw28105step1Labels := by
      have ha : raw28105step1 = (fun i j => raw28105step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28105step1 raw28105step0; decide +kernel
      have hl : raw28105step1Labels = raw28105step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28105step0 raw28105step0Labels permutation32 permutation5
    mixedMoment B raw28105step1 raw28105step1Labels = mixedMoment B raw28105step2 raw28105step2Labels := by
      have ha : raw28105step2 = -raw28105step1 := by apply Matrix.ext; change ∀ i j, raw28105step2 i j = -(raw28105step1 i j); unfold raw28105step2 raw28105step1; decide +kernel
      have hl : raw28105step2Labels = raw28105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28105step2 raw28105step2Labels = mixedMoment B raw28105step3 raw28105step3Labels := by
      have ha : raw28105step3 = raw28105step2 := by apply Matrix.ext; unfold raw28105step3 raw28105step2; decide +kernel
      have hl : raw28105step2Labels = labelEmbedding1 ∘ raw28105step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28105step2 raw28105step2Labels raw28105step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw28106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw28106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28106 raw28106Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw28106 raw28106Labels = mixedMoment B raw28106step0 raw28106step0Labels := by
      have hz : ∀ j, raw28106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28106step0 = (fun i j => raw28106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28106step0 raw28106; decide +kernel
      have hl : raw28106step0Labels = raw28106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28106 raw28106Labels permutation346 hz
    mixedMoment B raw28106step0 raw28106step0Labels = mixedMoment B raw28106step1 raw28106step1Labels := by
      have ha : raw28106step1 = (fun i j => raw28106step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28106step1 raw28106step0; decide +kernel
      have hl : raw28106step1Labels = raw28106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28106step0 raw28106step0Labels permutation151 permutation7
    mixedMoment B raw28106step1 raw28106step1Labels = mixedMoment B raw28106step2 raw28106step2Labels := by
      have ha : raw28106step2 = raw28106step1 := by apply Matrix.ext; unfold raw28106step2 raw28106step1; decide +kernel
      have hl : raw28106step1Labels = labelEmbedding1 ∘ raw28106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28106step1 raw28106step1Labels raw28106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw28107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28107 raw28107Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw28107 raw28107Labels = mixedMoment B raw28107step0 raw28107step0Labels := by
      have ha : raw28107step0 = (fun i j => raw28107 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28107step0 raw28107; decide +kernel
      have hl : raw28107step0Labels = raw28107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28107 raw28107Labels permutation682 permutation7
    mixedMoment B raw28107step0 raw28107step0Labels = mixedMoment B raw28107step1 raw28107step1Labels := by
      have ha : raw28107step1 = raw28107step0 := by apply Matrix.ext; unfold raw28107step1 raw28107step0; decide +kernel
      have hl : raw28107step0Labels = labelEmbedding1 ∘ raw28107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28107step0 raw28107step0Labels raw28107step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw28108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw28108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28108 raw28108Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw28108 raw28108Labels = mixedMoment B raw28108step0 raw28108step0Labels := by
      have hz : ∀ j, raw28108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28108step0 = (fun i j => raw28108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28108step0 raw28108; decide +kernel
      have hl : raw28108step0Labels = raw28108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28108 raw28108Labels permutation346 hz
    mixedMoment B raw28108step0 raw28108step0Labels = mixedMoment B raw28108step1 raw28108step1Labels := by
      have ha : raw28108step1 = (fun i j => raw28108step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28108step1 raw28108step0; decide +kernel
      have hl : raw28108step1Labels = raw28108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28108step0 raw28108step0Labels permutation149 permutation7
    mixedMoment B raw28108step1 raw28108step1Labels = mixedMoment B raw28108step2 raw28108step2Labels := by
      have ha : raw28108step2 = raw28108step1 := by apply Matrix.ext; unfold raw28108step2 raw28108step1; decide +kernel
      have hl : raw28108step1Labels = labelEmbedding1 ∘ raw28108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28108step1 raw28108step1Labels raw28108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw28109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw28109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw28109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw28109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28109step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28109 raw28109Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw28109 raw28109Labels = mixedMoment B raw28109step0 raw28109step0Labels := by
      have hz : ∀ j, raw28109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28109step0 = (fun i j => raw28109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28109step0 raw28109; decide +kernel
      have hl : raw28109step0Labels = raw28109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28109 raw28109Labels permutation520 hz
    mixedMoment B raw28109step0 raw28109step0Labels = mixedMoment B raw28109step1 raw28109step1Labels := by
      have hz : ∀ j, raw28109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28109step1 = (fun i j => raw28109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28109step1 raw28109step0; decide +kernel
      have hl : raw28109step1Labels = raw28109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28109step0 raw28109step0Labels permutation80 hz
    mixedMoment B raw28109step1 raw28109step1Labels = mixedMoment B raw28109step2 raw28109step2Labels := by
      have ha : raw28109step2 = (fun i j => raw28109step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28109step2 raw28109step1; decide +kernel
      have hl : raw28109step2Labels = raw28109step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28109step1 raw28109step1Labels permutation31 permutation7
    mixedMoment B raw28109step2 raw28109step2Labels = mixedMoment B raw28109step3 raw28109step3Labels := by
      have ha : raw28109step3 = raw28109step2 := by apply Matrix.ext; unfold raw28109step3 raw28109step2; decide +kernel
      have hl : raw28109step2Labels = labelEmbedding1 ∘ raw28109step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28109step2 raw28109step2Labels raw28109step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw28110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28110 raw28110Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw28110 raw28110Labels = mixedMoment B raw28110step0 raw28110step0Labels := by
      have hz : ∀ j, raw28110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28110step0 = (fun i j => raw28110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28110step0 raw28110; decide +kernel
      have hl : raw28110step0Labels = raw28110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28110 raw28110Labels permutation346 hz
    mixedMoment B raw28110step0 raw28110step0Labels = mixedMoment B raw28110step1 raw28110step1Labels := by
      have ha : raw28110step1 = (fun i j => raw28110step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28110step1 raw28110step0; decide +kernel
      have hl : raw28110step1Labels = raw28110step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28110step0 raw28110step0Labels permutation150 permutation2
    mixedMoment B raw28110step1 raw28110step1Labels = mixedMoment B raw28110step2 raw28110step2Labels := by
      have ha : raw28110step2 = -raw28110step1 := by apply Matrix.ext; change ∀ i j, raw28110step2 i j = -(raw28110step1 i j); unfold raw28110step2 raw28110step1; decide +kernel
      have hl : raw28110step2Labels = raw28110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw28111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28111 raw28111Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28111 raw28111Labels = mixedMoment B raw28111step0 raw28111step0Labels := by
      have hz : ∀ j, raw28111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28111step0 = (fun i j => raw28111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28111step0 raw28111; decide +kernel
      have hl : raw28111step0Labels = raw28111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28111 raw28111Labels permutation346 hz
    mixedMoment B raw28111step0 raw28111step0Labels = mixedMoment B raw28111step1 raw28111step1Labels := by
      have ha : raw28111step1 = (fun i j => raw28111step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28111step1 raw28111step0; decide +kernel
      have hl : raw28111step1Labels = raw28111step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28111step0 raw28111step0Labels permutation151 permutation2
    mixedMoment B raw28111step1 raw28111step1Labels = mixedMoment B raw28111step2 raw28111step2Labels := by
      have ha : raw28111step2 = -raw28111step1 := by apply Matrix.ext; change ∀ i j, raw28111step2 i j = -(raw28111step1 i j); unfold raw28111step2 raw28111step1; decide +kernel
      have hl : raw28111step2Labels = raw28111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28112 raw28112Labels = mixedMoment B node1956 node1956Labels := by
  calc
    mixedMoment B raw28112 raw28112Labels = mixedMoment B raw28112step0 raw28112step0Labels := by
      have ha : raw28112step0 = (fun i j => raw28112 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28112step0 raw28112; decide +kernel
      have hl : raw28112step0Labels = raw28112Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28112 raw28112Labels permutation646 permutation2
    mixedMoment B raw28112step0 raw28112step0Labels = mixedMoment B raw28112step1 raw28112step1Labels := by
      have ha : raw28112step1 = -raw28112step0 := by apply Matrix.ext; change ∀ i j, raw28112step1 i j = -(raw28112step0 i j); unfold raw28112step1 raw28112step0; decide +kernel
      have hl : raw28112step1Labels = raw28112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1956 node1956Labels := by rfl

def raw28113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28113 raw28113Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw28113 raw28113Labels = mixedMoment B raw28113step0 raw28113step0Labels := by
      have hz : ∀ j, raw28113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28113step0 = (fun i j => raw28113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28113step0 raw28113; decide +kernel
      have hl : raw28113step0Labels = raw28113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28113 raw28113Labels permutation346 hz
    mixedMoment B raw28113step0 raw28113step0Labels = mixedMoment B raw28113step1 raw28113step1Labels := by
      have ha : raw28113step1 = (fun i j => raw28113step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28113step1 raw28113step0; decide +kernel
      have hl : raw28113step1Labels = raw28113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28113step0 raw28113step0Labels permutation151 permutation2
    mixedMoment B raw28113step1 raw28113step1Labels = mixedMoment B raw28113step2 raw28113step2Labels := by
      have ha : raw28113step2 = -raw28113step1 := by apply Matrix.ext; change ∀ i j, raw28113step2 i j = -(raw28113step1 i j); unfold raw28113step2 raw28113step1; decide +kernel
      have hl : raw28113step2Labels = raw28113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1979 node1979Labels := by rfl

def raw28114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28114 raw28114Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw28114 raw28114Labels = mixedMoment B raw28114step0 raw28114step0Labels := by
      have hz : ∀ j, raw28114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28114step0 = (fun i j => raw28114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28114step0 raw28114; decide +kernel
      have hl : raw28114step0Labels = raw28114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28114 raw28114Labels permutation346 hz
    mixedMoment B raw28114step0 raw28114step0Labels = mixedMoment B raw28114step1 raw28114step1Labels := by
      have ha : raw28114step1 = (fun i j => raw28114step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28114step1 raw28114step0; decide +kernel
      have hl : raw28114step1Labels = raw28114step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28114step0 raw28114step0Labels permutation151 permutation2
    mixedMoment B raw28114step1 raw28114step1Labels = mixedMoment B raw28114step2 raw28114step2Labels := by
      have ha : raw28114step2 = -raw28114step1 := by apply Matrix.ext; change ∀ i j, raw28114step2 i j = -(raw28114step1 i j); unfold raw28114step2 raw28114step1; decide +kernel
      have hl : raw28114step2Labels = raw28114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1796 node1796Labels := by rfl

def raw28115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw28115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw28115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28115 raw28115Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw28115 raw28115Labels = mixedMoment B raw28115step0 raw28115step0Labels := by
      have hz : ∀ j, raw28115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28115step0 = (fun i j => raw28115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28115step0 raw28115; decide +kernel
      have hl : raw28115step0Labels = raw28115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28115 raw28115Labels permutation346 hz
    mixedMoment B raw28115step0 raw28115step0Labels = mixedMoment B raw28115step1 raw28115step1Labels := by
      have ha : raw28115step1 = (fun i j => raw28115step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28115step1 raw28115step0; decide +kernel
      have hl : raw28115step1Labels = raw28115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28115step0 raw28115step0Labels permutation151 permutation2
    mixedMoment B raw28115step1 raw28115step1Labels = mixedMoment B raw28115step2 raw28115step2Labels := by
      have ha : raw28115step2 = -raw28115step1 := by apply Matrix.ext; change ∀ i j, raw28115step2 i j = -(raw28115step1 i j); unfold raw28115step2 raw28115step1; decide +kernel
      have hl : raw28115step2Labels = raw28115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node913 node913Labels := by rfl

def raw28116 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw28116Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw28116step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw28116step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw28116step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28116step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw28116step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28116 raw28116Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw28116 raw28116Labels = mixedMoment B raw28116step0 raw28116step0Labels := by
      have hz : ∀ j, raw28116 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28116step0 = (fun i j => raw28116 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28116step0 raw28116; decide +kernel
      have hl : raw28116step0Labels = raw28116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28116 raw28116Labels permutation520 hz
    mixedMoment B raw28116step0 raw28116step0Labels = mixedMoment B raw28116step1 raw28116step1Labels := by
      have hz : ∀ j, raw28116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28116step1 = (fun i j => raw28116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28116step1 raw28116step0; decide +kernel
      have hl : raw28116step1Labels = raw28116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28116step0 raw28116step0Labels permutation80 hz
    mixedMoment B raw28116step1 raw28116step1Labels = mixedMoment B raw28116step2 raw28116step2Labels := by
      have ha : raw28116step2 = (fun i j => raw28116step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28116step2 raw28116step1; decide +kernel
      have hl : raw28116step2Labels = raw28116step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28116step1 raw28116step1Labels permutation26 permutation0
    mixedMoment B raw28116step2 raw28116step2Labels = mixedMoment B raw28116step3 raw28116step3Labels := by
      have ha : raw28116step3 = -raw28116step2 := by apply Matrix.ext; change ∀ i j, raw28116step3 i j = -(raw28116step2 i j); unfold raw28116step3 raw28116step2; decide +kernel
      have hl : raw28116step3Labels = raw28116step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw28117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28117 raw28117Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw28117 raw28117Labels = mixedMoment B raw28117step0 raw28117step0Labels := by
      have ha : raw28117step0 = (fun i j => raw28117 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28117step0 raw28117; decide +kernel
      have hl : raw28117step0Labels = raw28117Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28117 raw28117Labels permutation158 permutation2
    _ = mixedMoment B node1326 node1326Labels := by rfl

def raw28118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28118 raw28118Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw28118 raw28118Labels = mixedMoment B raw28118step0 raw28118step0Labels := by
      have ha : raw28118step0 = (fun i j => raw28118 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28118step0 raw28118; decide +kernel
      have hl : raw28118step0Labels = raw28118Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28118 raw28118Labels permutation644 permutation2
    mixedMoment B raw28118step0 raw28118step0Labels = mixedMoment B raw28118step1 raw28118step1Labels := by
      have ha : raw28118step1 = -raw28118step0 := by apply Matrix.ext; change ∀ i j, raw28118step1 i j = -(raw28118step0 i j); unfold raw28118step1 raw28118step0; decide +kernel
      have hl : raw28118step1Labels = raw28118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw28119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw28119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28119 raw28119Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28119 raw28119Labels = mixedMoment B raw28119step0 raw28119step0Labels := by
      have hz : ∀ j, raw28119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28119step0 = (fun i j => raw28119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28119step0 raw28119; decide +kernel
      have hl : raw28119step0Labels = raw28119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28119 raw28119Labels permutation520 hz
    mixedMoment B raw28119step0 raw28119step0Labels = mixedMoment B raw28119step1 raw28119step1Labels := by
      have ha : raw28119step1 = (fun i j => raw28119step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28119step1 raw28119step0; decide +kernel
      have hl : raw28119step1Labels = raw28119step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28119step0 raw28119step0Labels permutation145 permutation2
    mixedMoment B raw28119step1 raw28119step1Labels = mixedMoment B raw28119step2 raw28119step2Labels := by
      have ha : raw28119step2 = -raw28119step1 := by apply Matrix.ext; change ∀ i j, raw28119step2 i j = -(raw28119step1 i j); unfold raw28119step2 raw28119step1; decide +kernel
      have hl : raw28119step2Labels = raw28119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28120 raw28120Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw28120 raw28120Labels = mixedMoment B raw28120step0 raw28120step0Labels := by
      have ha : raw28120step0 = (fun i j => raw28120 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28120step0 raw28120; decide +kernel
      have hl : raw28120step0Labels = raw28120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28120 raw28120Labels permutation158 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw28121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28121 raw28121Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw28121 raw28121Labels = mixedMoment B raw28121step0 raw28121step0Labels := by
      have hz : ∀ j, raw28121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28121step0 = (fun i j => raw28121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28121step0 raw28121; decide +kernel
      have hl : raw28121step0Labels = raw28121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28121 raw28121Labels permutation346 hz
    mixedMoment B raw28121step0 raw28121step0Labels = mixedMoment B raw28121step1 raw28121step1Labels := by
      have ha : raw28121step1 = (fun i j => raw28121step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28121step1 raw28121step0; decide +kernel
      have hl : raw28121step1Labels = raw28121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28121step0 raw28121step0Labels permutation149 permutation2
    mixedMoment B raw28121step1 raw28121step1Labels = mixedMoment B raw28121step2 raw28121step2Labels := by
      have ha : raw28121step2 = -raw28121step1 := by apply Matrix.ext; change ∀ i j, raw28121step2 i j = -(raw28121step1 i j); unfold raw28121step2 raw28121step1; decide +kernel
      have hl : raw28121step2Labels = raw28121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2057 node2057Labels := by rfl

def raw28122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw28122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28122 raw28122Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28122 raw28122Labels = mixedMoment B raw28122step0 raw28122step0Labels := by
      have hz : ∀ j, raw28122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28122step0 = (fun i j => raw28122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28122step0 raw28122; decide +kernel
      have hl : raw28122step0Labels = raw28122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28122 raw28122Labels permutation346 hz
    mixedMoment B raw28122step0 raw28122step0Labels = mixedMoment B raw28122step1 raw28122step1Labels := by
      have ha : raw28122step1 = (fun i j => raw28122step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28122step1 raw28122step0; decide +kernel
      have hl : raw28122step1Labels = raw28122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28122step0 raw28122step0Labels permutation149 permutation2
    mixedMoment B raw28122step1 raw28122step1Labels = mixedMoment B raw28122step2 raw28122step2Labels := by
      have ha : raw28122step2 = -raw28122step1 := by apply Matrix.ext; change ∀ i j, raw28122step2 i j = -(raw28122step1 i j); unfold raw28122step2 raw28122step1; decide +kernel
      have hl : raw28122step2Labels = raw28122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw28123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28123 raw28123Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw28123 raw28123Labels = mixedMoment B raw28123step0 raw28123step0Labels := by
      have hz : ∀ j, raw28123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28123step0 = (fun i j => raw28123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28123step0 raw28123; decide +kernel
      have hl : raw28123step0Labels = raw28123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28123 raw28123Labels permutation346 hz
    mixedMoment B raw28123step0 raw28123step0Labels = mixedMoment B raw28123step1 raw28123step1Labels := by
      have ha : raw28123step1 = (fun i j => raw28123step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28123step1 raw28123step0; decide +kernel
      have hl : raw28123step1Labels = raw28123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28123step0 raw28123step0Labels permutation149 permutation2
    mixedMoment B raw28123step1 raw28123step1Labels = mixedMoment B raw28123step2 raw28123step2Labels := by
      have ha : raw28123step2 = -raw28123step1 := by apply Matrix.ext; change ∀ i j, raw28123step2 i j = -(raw28123step1 i j); unfold raw28123step2 raw28123step1; decide +kernel
      have hl : raw28123step2Labels = raw28123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw28124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw28124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28124 raw28124Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw28124 raw28124Labels = mixedMoment B raw28124step0 raw28124step0Labels := by
      have hz : ∀ j, raw28124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28124step0 = (fun i j => raw28124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28124step0 raw28124; decide +kernel
      have hl : raw28124step0Labels = raw28124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28124 raw28124Labels permutation346 hz
    mixedMoment B raw28124step0 raw28124step0Labels = mixedMoment B raw28124step1 raw28124step1Labels := by
      have ha : raw28124step1 = (fun i j => raw28124step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28124step1 raw28124step0; decide +kernel
      have hl : raw28124step1Labels = raw28124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28124step0 raw28124step0Labels permutation149 permutation2
    mixedMoment B raw28124step1 raw28124step1Labels = mixedMoment B raw28124step2 raw28124step2Labels := by
      have ha : raw28124step2 = -raw28124step1 := by apply Matrix.ext; change ∀ i j, raw28124step2 i j = -(raw28124step1 i j); unfold raw28124step2 raw28124step1; decide +kernel
      have hl : raw28124step2Labels = raw28124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

def raw28125 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28125step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28125step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28125step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28125step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28125 raw28125Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28125 raw28125Labels = mixedMoment B raw28125step0 raw28125step0Labels := by
      have hz : ∀ j, raw28125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28125step0 = (fun i j => raw28125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28125step0 raw28125; decide +kernel
      have hl : raw28125step0Labels = raw28125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28125 raw28125Labels permutation346 hz
    mixedMoment B raw28125step0 raw28125step0Labels = mixedMoment B raw28125step1 raw28125step1Labels := by
      have ha : raw28125step1 = (fun i j => raw28125step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28125step1 raw28125step0; decide +kernel
      have hl : raw28125step1Labels = raw28125step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28125step0 raw28125step0Labels permutation151 permutation7
    mixedMoment B raw28125step1 raw28125step1Labels = mixedMoment B raw28125step2 raw28125step2Labels := by
      have ha : raw28125step2 = -raw28125step1 := by apply Matrix.ext; change ∀ i j, raw28125step2 i j = -(raw28125step1 i j); unfold raw28125step2 raw28125step1; decide +kernel
      have hl : raw28125step2Labels = raw28125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28125step2 raw28125step2Labels = mixedMoment B raw28125step3 raw28125step3Labels := by
      have ha : raw28125step3 = raw28125step2 := by apply Matrix.ext; unfold raw28125step3 raw28125step2; decide +kernel
      have hl : raw28125step2Labels = labelEmbedding10 ∘ raw28125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28125step2 raw28125step2Labels raw28125step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw28126 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28126step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28126step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28126step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28126step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28126 raw28126Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw28126 raw28126Labels = mixedMoment B raw28126step0 raw28126step0Labels := by
      have ha : raw28126step0 = (fun i j => raw28126 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28126step0 raw28126; decide +kernel
      have hl : raw28126step0Labels = raw28126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28126 raw28126Labels permutation682 permutation7
    mixedMoment B raw28126step0 raw28126step0Labels = mixedMoment B raw28126step1 raw28126step1Labels := by
      have ha : raw28126step1 = -raw28126step0 := by apply Matrix.ext; change ∀ i j, raw28126step1 i j = -(raw28126step0 i j); unfold raw28126step1 raw28126step0; decide +kernel
      have hl : raw28126step1Labels = raw28126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28126step1 raw28126step1Labels = mixedMoment B raw28126step2 raw28126step2Labels := by
      have ha : raw28126step2 = raw28126step1 := by apply Matrix.ext; unfold raw28126step2 raw28126step1; decide +kernel
      have hl : raw28126step1Labels = labelEmbedding10 ∘ raw28126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28126step1 raw28126step1Labels raw28126step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw28127 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28127 raw28127Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw28127 raw28127Labels = mixedMoment B raw28127step0 raw28127step0Labels := by
      have hz : ∀ j, raw28127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28127step0 = (fun i j => raw28127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28127step0 raw28127; decide +kernel
      have hl : raw28127step0Labels = raw28127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28127 raw28127Labels permutation346 hz
    mixedMoment B raw28127step0 raw28127step0Labels = mixedMoment B raw28127step1 raw28127step1Labels := by
      have ha : raw28127step1 = (fun i j => raw28127step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28127step1 raw28127step0; decide +kernel
      have hl : raw28127step1Labels = raw28127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28127step0 raw28127step0Labels permutation151 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw28128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw28128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28128step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28128 raw28128Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw28128 raw28128Labels = mixedMoment B raw28128step0 raw28128step0Labels := by
      have hz : ∀ j, raw28128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28128step0 = (fun i j => raw28128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28128step0 raw28128; decide +kernel
      have hl : raw28128step0Labels = raw28128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28128 raw28128Labels permutation346 hz
    mixedMoment B raw28128step0 raw28128step0Labels = mixedMoment B raw28128step1 raw28128step1Labels := by
      have ha : raw28128step1 = (fun i j => raw28128step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28128step1 raw28128step0; decide +kernel
      have hl : raw28128step1Labels = raw28128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28128step0 raw28128step0Labels permutation151 permutation7
    mixedMoment B raw28128step1 raw28128step1Labels = mixedMoment B raw28128step2 raw28128step2Labels := by
      have ha : raw28128step2 = -raw28128step1 := by apply Matrix.ext; change ∀ i j, raw28128step2 i j = -(raw28128step1 i j); unfold raw28128step2 raw28128step1; decide +kernel
      have hl : raw28128step2Labels = raw28128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28128step2 raw28128step2Labels = mixedMoment B raw28128step3 raw28128step3Labels := by
      have ha : raw28128step3 = raw28128step2 := by apply Matrix.ext; unfold raw28128step3 raw28128step2; decide +kernel
      have hl : raw28128step2Labels = labelEmbedding10 ∘ raw28128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28128step2 raw28128step2Labels raw28128step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw28129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28129step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28129 raw28129Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw28129 raw28129Labels = mixedMoment B raw28129step0 raw28129step0Labels := by
      have ha : raw28129step0 = (fun i j => raw28129 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28129step0 raw28129; decide +kernel
      have hl : raw28129step0Labels = raw28129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28129 raw28129Labels permutation682 permutation7
    mixedMoment B raw28129step0 raw28129step0Labels = mixedMoment B raw28129step1 raw28129step1Labels := by
      have ha : raw28129step1 = -raw28129step0 := by apply Matrix.ext; change ∀ i j, raw28129step1 i j = -(raw28129step0 i j); unfold raw28129step1 raw28129step0; decide +kernel
      have hl : raw28129step1Labels = raw28129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28129step1 raw28129step1Labels = mixedMoment B raw28129step2 raw28129step2Labels := by
      have ha : raw28129step2 = raw28129step1 := by apply Matrix.ext; unfold raw28129step2 raw28129step1; decide +kernel
      have hl : raw28129step1Labels = labelEmbedding10 ∘ raw28129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28129step1 raw28129step1Labels raw28129step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw28130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw28130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28130 raw28130Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw28130 raw28130Labels = mixedMoment B raw28130step0 raw28130step0Labels := by
      have hz : ∀ j, raw28130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28130step0 = (fun i j => raw28130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28130step0 raw28130; decide +kernel
      have hl : raw28130step0Labels = raw28130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28130 raw28130Labels permutation346 hz
    mixedMoment B raw28130step0 raw28130step0Labels = mixedMoment B raw28130step1 raw28130step1Labels := by
      have ha : raw28130step1 = (fun i j => raw28130step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28130step1 raw28130step0; decide +kernel
      have hl : raw28130step1Labels = raw28130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28130step0 raw28130step0Labels permutation150 permutation2
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw28131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28131step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28131 raw28131Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw28131 raw28131Labels = mixedMoment B raw28131step0 raw28131step0Labels := by
      have ha : raw28131step0 = (fun i j => raw28131 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28131step0 raw28131; decide +kernel
      have hl : raw28131step0Labels = raw28131Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28131 raw28131Labels permutation152 permutation6
    mixedMoment B raw28131step0 raw28131step0Labels = mixedMoment B raw28131step1 raw28131step1Labels := by
      have ha : raw28131step1 = raw28131step0 := by apply Matrix.ext; unfold raw28131step1 raw28131step0; decide +kernel
      have hl : raw28131step0Labels = labelEmbedding9 ∘ raw28131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28131step0 raw28131step0Labels raw28131step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw28132 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28132step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28132 raw28132Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw28132 raw28132Labels = mixedMoment B raw28132step0 raw28132step0Labels := by
      have ha : raw28132step0 = (fun i j => raw28132 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28132step0 raw28132; decide +kernel
      have hl : raw28132step0Labels = raw28132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28132 raw28132Labels permutation682 permutation7
    mixedMoment B raw28132step0 raw28132step0Labels = mixedMoment B raw28132step1 raw28132step1Labels := by
      have ha : raw28132step1 = -raw28132step0 := by apply Matrix.ext; change ∀ i j, raw28132step1 i j = -(raw28132step0 i j); unfold raw28132step1 raw28132step0; decide +kernel
      have hl : raw28132step1Labels = raw28132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28132step1 raw28132step1Labels = mixedMoment B raw28132step2 raw28132step2Labels := by
      have ha : raw28132step2 = raw28132step1 := by apply Matrix.ext; unfold raw28132step2 raw28132step1; decide +kernel
      have hl : raw28132step1Labels = labelEmbedding10 ∘ raw28132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28132step1 raw28132step1Labels raw28132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw28133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw28133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28133 raw28133Labels = mixedMoment B node4414 node4414Labels := by
  calc
    mixedMoment B raw28133 raw28133Labels = mixedMoment B raw28133step0 raw28133step0Labels := by
      have ha : raw28133step0 = (fun i j => raw28133 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28133step0 raw28133; decide +kernel
      have hl : raw28133step0Labels = raw28133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28133 raw28133Labels permutation682 permutation2
    _ = mixedMoment B node4414 node4414Labels := by rfl

def raw28134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28134 raw28134Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw28134 raw28134Labels = mixedMoment B raw28134step0 raw28134step0Labels := by
      have hz : ∀ j, raw28134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28134step0 = (fun i j => raw28134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28134step0 raw28134; decide +kernel
      have hl : raw28134step0Labels = raw28134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28134 raw28134Labels permutation346 hz
    mixedMoment B raw28134step0 raw28134step0Labels = mixedMoment B raw28134step1 raw28134step1Labels := by
      have ha : raw28134step1 = (fun i j => raw28134step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28134step1 raw28134step0; decide +kernel
      have hl : raw28134step1Labels = raw28134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28134step0 raw28134step0Labels permutation32 permutation6
    mixedMoment B raw28134step1 raw28134step1Labels = mixedMoment B raw28134step2 raw28134step2Labels := by
      have ha : raw28134step2 = raw28134step1 := by apply Matrix.ext; unfold raw28134step2 raw28134step1; decide +kernel
      have hl : raw28134step1Labels = labelEmbedding9 ∘ raw28134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28134step1 raw28134step1Labels raw28134step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw28135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28135step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28135step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28135 raw28135Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw28135 raw28135Labels = mixedMoment B raw28135step0 raw28135step0Labels := by
      have hz : ∀ j, raw28135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28135step0 = (fun i j => raw28135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28135step0 raw28135; decide +kernel
      have hl : raw28135step0Labels = raw28135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28135 raw28135Labels permutation346 hz
    mixedMoment B raw28135step0 raw28135step0Labels = mixedMoment B raw28135step1 raw28135step1Labels := by
      have ha : raw28135step1 = (fun i j => raw28135step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28135step1 raw28135step0; decide +kernel
      have hl : raw28135step1Labels = raw28135step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28135step0 raw28135step0Labels permutation151 permutation7
    mixedMoment B raw28135step1 raw28135step1Labels = mixedMoment B raw28135step2 raw28135step2Labels := by
      have ha : raw28135step2 = -raw28135step1 := by apply Matrix.ext; change ∀ i j, raw28135step2 i j = -(raw28135step1 i j); unfold raw28135step2 raw28135step1; decide +kernel
      have hl : raw28135step2Labels = raw28135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28135step2 raw28135step2Labels = mixedMoment B raw28135step3 raw28135step3Labels := by
      have ha : raw28135step3 = raw28135step2 := by apply Matrix.ext; unfold raw28135step3 raw28135step2; decide +kernel
      have hl : raw28135step2Labels = labelEmbedding10 ∘ raw28135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28135step2 raw28135step2Labels raw28135step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw28136 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw28136step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28136step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw28136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28136 raw28136Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw28136 raw28136Labels = mixedMoment B raw28136step0 raw28136step0Labels := by
      have ha : raw28136step0 = (fun i j => raw28136 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28136step0 raw28136; decide +kernel
      have hl : raw28136step0Labels = raw28136Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28136 raw28136Labels permutation682 permutation7
    mixedMoment B raw28136step0 raw28136step0Labels = mixedMoment B raw28136step1 raw28136step1Labels := by
      have ha : raw28136step1 = -raw28136step0 := by apply Matrix.ext; change ∀ i j, raw28136step1 i j = -(raw28136step0 i j); unfold raw28136step1 raw28136step0; decide +kernel
      have hl : raw28136step1Labels = raw28136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28136step1 raw28136step1Labels = mixedMoment B raw28136step2 raw28136step2Labels := by
      have ha : raw28136step2 = raw28136step1 := by apply Matrix.ext; unfold raw28136step2 raw28136step1; decide +kernel
      have hl : raw28136step1Labels = labelEmbedding10 ∘ raw28136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28136step1 raw28136step1Labels raw28136step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

def raw28137 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw28137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28137 raw28137Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw28137 raw28137Labels = mixedMoment B raw28137step0 raw28137step0Labels := by
      have hz : ∀ j, raw28137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28137step0 = (fun i j => raw28137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28137step0 raw28137; decide +kernel
      have hl : raw28137step0Labels = raw28137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28137 raw28137Labels permutation346 hz
    mixedMoment B raw28137step0 raw28137step0Labels = mixedMoment B raw28137step1 raw28137step1Labels := by
      have ha : raw28137step1 = (fun i j => raw28137step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28137step1 raw28137step0; decide +kernel
      have hl : raw28137step1Labels = raw28137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28137step0 raw28137step0Labels permutation148 permutation2
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw28138 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28138 raw28138Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28138 raw28138Labels = mixedMoment B raw28138step0 raw28138step0Labels := by
      have hz : ∀ j, raw28138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28138step0 = (fun i j => raw28138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28138step0 raw28138; decide +kernel
      have hl : raw28138step0Labels = raw28138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28138 raw28138Labels permutation346 hz
    mixedMoment B raw28138step0 raw28138step0Labels = mixedMoment B raw28138step1 raw28138step1Labels := by
      have ha : raw28138step1 = (fun i j => raw28138step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28138step1 raw28138step0; decide +kernel
      have hl : raw28138step1Labels = raw28138step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28138step0 raw28138step0Labels permutation32 permutation6
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28139 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28139 raw28139Labels = mixedMoment B node2982 node2982Labels := by
  calc
    mixedMoment B raw28139 raw28139Labels = mixedMoment B raw28139step0 raw28139step0Labels := by
      have ha : raw28139step0 = (fun i j => raw28139 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28139step0 raw28139; decide +kernel
      have hl : raw28139step0Labels = raw28139Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28139 raw28139Labels permutation152 permutation6
    _ = mixedMoment B node2982 node2982Labels := by rfl

def raw28140 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw28140step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28140 raw28140Labels = mixedMoment B node3004 node3004Labels := by
  calc
    mixedMoment B raw28140 raw28140Labels = mixedMoment B raw28140step0 raw28140step0Labels := by
      have hz : ∀ j, raw28140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28140step0 = (fun i j => raw28140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28140step0 raw28140; decide +kernel
      have hl : raw28140step0Labels = raw28140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28140 raw28140Labels permutation434 hz
    mixedMoment B raw28140step0 raw28140step0Labels = mixedMoment B raw28140step1 raw28140step1Labels := by
      have hz : ∀ j, raw28140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28140step1 = (fun i j => raw28140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28140step1 raw28140step0; decide +kernel
      have hl : raw28140step1Labels = raw28140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28140step0 raw28140step0Labels permutation80 hz
    mixedMoment B raw28140step1 raw28140step1Labels = mixedMoment B raw28140step2 raw28140step2Labels := by
      have ha : raw28140step2 = (fun i j => raw28140step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28140step2 raw28140step1; decide +kernel
      have hl : raw28140step2Labels = raw28140step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28140step1 raw28140step1Labels permutation8 permutation6
    _ = mixedMoment B node3004 node3004Labels := by rfl

def raw28141 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28141 raw28141Labels = mixedMoment B node2993 node2993Labels := by
  calc
    mixedMoment B raw28141 raw28141Labels = mixedMoment B raw28141step0 raw28141step0Labels := by
      have hz : ∀ j, raw28141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28141step0 = (fun i j => raw28141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28141step0 raw28141; decide +kernel
      have hl : raw28141step0Labels = raw28141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28141 raw28141Labels permutation346 hz
    mixedMoment B raw28141step0 raw28141step0Labels = mixedMoment B raw28141step1 raw28141step1Labels := by
      have ha : raw28141step1 = (fun i j => raw28141step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28141step1 raw28141step0; decide +kernel
      have hl : raw28141step1Labels = raw28141step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28141step0 raw28141step0Labels permutation32 permutation6
    _ = mixedMoment B node2993 node2993Labels := by rfl

def raw28142 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw28142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28142 raw28142Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw28142 raw28142Labels = mixedMoment B raw28142step0 raw28142step0Labels := by
      have hz : ∀ j, raw28142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28142step0 = (fun i j => raw28142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28142step0 raw28142; decide +kernel
      have hl : raw28142step0Labels = raw28142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28142 raw28142Labels permutation346 hz
    mixedMoment B raw28142step0 raw28142step0Labels = mixedMoment B raw28142step1 raw28142step1Labels := by
      have ha : raw28142step1 = (fun i j => raw28142step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28142step1 raw28142step0; decide +kernel
      have hl : raw28142step1Labels = raw28142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28142step0 raw28142step0Labels permutation149 permutation3
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw28143 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28143 raw28143Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw28143 raw28143Labels = mixedMoment B raw28143step0 raw28143step0Labels := by
      have hz : ∀ j, raw28143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28143step0 = (fun i j => raw28143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28143step0 raw28143; decide +kernel
      have hl : raw28143step0Labels = raw28143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28143 raw28143Labels permutation346 hz
    mixedMoment B raw28143step0 raw28143step0Labels = mixedMoment B raw28143step1 raw28143step1Labels := by
      have ha : raw28143step1 = (fun i j => raw28143step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28143step1 raw28143step0; decide +kernel
      have hl : raw28143step1Labels = raw28143step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28143step0 raw28143step0Labels permutation32 permutation6
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw28144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28144 raw28144Labels = mixedMoment B node2611 node2611Labels := by
  calc
    mixedMoment B raw28144 raw28144Labels = mixedMoment B raw28144step0 raw28144step0Labels := by
      have ha : raw28144step0 = (fun i j => raw28144 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28144step0 raw28144; decide +kernel
      have hl : raw28144step0Labels = raw28144Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28144 raw28144Labels permutation152 permutation6
    _ = mixedMoment B node2611 node2611Labels := by rfl

def raw28145 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw28145step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28145 raw28145Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw28145 raw28145Labels = mixedMoment B raw28145step0 raw28145step0Labels := by
      have hz : ∀ j, raw28145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28145step0 = (fun i j => raw28145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28145step0 raw28145; decide +kernel
      have hl : raw28145step0Labels = raw28145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28145 raw28145Labels permutation434 hz
    mixedMoment B raw28145step0 raw28145step0Labels = mixedMoment B raw28145step1 raw28145step1Labels := by
      have hz : ∀ j, raw28145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28145step1 = (fun i j => raw28145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28145step1 raw28145step0; decide +kernel
      have hl : raw28145step1Labels = raw28145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28145step0 raw28145step0Labels permutation80 hz
    mixedMoment B raw28145step1 raw28145step1Labels = mixedMoment B raw28145step2 raw28145step2Labels := by
      have ha : raw28145step2 = (fun i j => raw28145step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28145step2 raw28145step1; decide +kernel
      have hl : raw28145step2Labels = raw28145step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28145step1 raw28145step1Labels permutation8 permutation6
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw28146 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28146 raw28146Labels = mixedMoment B node2626 node2626Labels := by
  calc
    mixedMoment B raw28146 raw28146Labels = mixedMoment B raw28146step0 raw28146step0Labels := by
      have hz : ∀ j, raw28146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28146step0 = (fun i j => raw28146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28146step0 raw28146; decide +kernel
      have hl : raw28146step0Labels = raw28146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28146 raw28146Labels permutation346 hz
    mixedMoment B raw28146step0 raw28146step0Labels = mixedMoment B raw28146step1 raw28146step1Labels := by
      have ha : raw28146step1 = (fun i j => raw28146step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28146step1 raw28146step0; decide +kernel
      have hl : raw28146step1Labels = raw28146step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28146step0 raw28146step0Labels permutation32 permutation6
    _ = mixedMoment B node2626 node2626Labels := by rfl

def raw28147 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw28147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28147 raw28147Labels = mixedMoment B node1423 node1423Labels := by
  calc
    mixedMoment B raw28147 raw28147Labels = mixedMoment B raw28147step0 raw28147step0Labels := by
      have hz : ∀ j, raw28147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28147step0 = (fun i j => raw28147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28147step0 raw28147; decide +kernel
      have hl : raw28147step0Labels = raw28147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28147 raw28147Labels permutation346 hz
    mixedMoment B raw28147step0 raw28147step0Labels = mixedMoment B raw28147step1 raw28147step1Labels := by
      have ha : raw28147step1 = (fun i j => raw28147step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28147step1 raw28147step0; decide +kernel
      have hl : raw28147step1Labels = raw28147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28147step0 raw28147step0Labels permutation147 permutation3
    _ = mixedMoment B node1423 node1423Labels := by rfl

def raw28148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28148 raw28148Labels = mixedMoment B node2010 node2010Labels := by
  calc
    mixedMoment B raw28148 raw28148Labels = mixedMoment B raw28148step0 raw28148step0Labels := by
      have ha : raw28148step0 = (fun i j => raw28148 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28148step0 raw28148; decide +kernel
      have hl : raw28148step0Labels = raw28148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28148 raw28148Labels permutation152 permutation6
    _ = mixedMoment B node2010 node2010Labels := by rfl

def raw28149 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28149 raw28149Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw28149 raw28149Labels = mixedMoment B raw28149step0 raw28149step0Labels := by
      have ha : raw28149step0 = (fun i j => raw28149 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28149step0 raw28149; decide +kernel
      have hl : raw28149step0Labels = raw28149Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28149 raw28149Labels permutation152 permutation6
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw28150 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28150 raw28150Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw28150 raw28150Labels = mixedMoment B raw28150step0 raw28150step0Labels := by
      have hz : ∀ j, raw28150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28150step0 = (fun i j => raw28150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28150step0 raw28150; decide +kernel
      have hl : raw28150step0Labels = raw28150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28150 raw28150Labels permutation434 hz
    mixedMoment B raw28150step0 raw28150step0Labels = mixedMoment B raw28150step1 raw28150step1Labels := by
      have ha : raw28150step1 = (fun i j => raw28150step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28150step1 raw28150step0; decide +kernel
      have hl : raw28150step1Labels = raw28150step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28150step0 raw28150step0Labels permutation32 permutation6
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw28151 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28151 raw28151Labels = mixedMoment B node2563 node2563Labels := by
  calc
    mixedMoment B raw28151 raw28151Labels = mixedMoment B raw28151step0 raw28151step0Labels := by
      have ha : raw28151step0 = (fun i j => raw28151 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28151step0 raw28151; decide +kernel
      have hl : raw28151step0Labels = raw28151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28151 raw28151Labels permutation152 permutation6
    _ = mixedMoment B node2563 node2563Labels := by rfl

def raw28152 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw28152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28152 raw28152Labels = mixedMoment B node1421 node1421Labels := by
  calc
    mixedMoment B raw28152 raw28152Labels = mixedMoment B raw28152step0 raw28152step0Labels := by
      have ha : raw28152step0 = (fun i j => raw28152 (permutation665 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28152step0 raw28152; decide +kernel
      have hl : raw28152step0Labels = raw28152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28152 raw28152Labels permutation665 permutation3
    _ = mixedMoment B node1421 node1421Labels := by rfl

def raw28153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28153 raw28153Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw28153 raw28153Labels = mixedMoment B raw28153step0 raw28153step0Labels := by
      have hz : ∀ j, raw28153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28153step0 = (fun i j => raw28153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28153step0 raw28153; decide +kernel
      have hl : raw28153step0Labels = raw28153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28153 raw28153Labels permutation346 hz
    mixedMoment B raw28153step0 raw28153step0Labels = mixedMoment B raw28153step1 raw28153step1Labels := by
      have ha : raw28153step1 = (fun i j => raw28153step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28153step1 raw28153step0; decide +kernel
      have hl : raw28153step1Labels = raw28153step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28153step0 raw28153step0Labels permutation32 permutation6
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw28154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28154 raw28154Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw28154 raw28154Labels = mixedMoment B raw28154step0 raw28154step0Labels := by
      have hz : ∀ j, raw28154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28154step0 = (fun i j => raw28154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28154step0 raw28154; decide +kernel
      have hl : raw28154step0Labels = raw28154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28154 raw28154Labels permutation346 hz
    mixedMoment B raw28154step0 raw28154step0Labels = mixedMoment B raw28154step1 raw28154step1Labels := by
      have ha : raw28154step1 = (fun i j => raw28154step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28154step1 raw28154step0; decide +kernel
      have hl : raw28154step1Labels = raw28154step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28154step0 raw28154step0Labels permutation32 permutation6
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw28155 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw28155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28155 raw28155Labels = mixedMoment B node2548 node2548Labels := by
  calc
    mixedMoment B raw28155 raw28155Labels = mixedMoment B raw28155step0 raw28155step0Labels := by
      have ha : raw28155step0 = (fun i j => raw28155 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28155step0 raw28155; decide +kernel
      have hl : raw28155step0Labels = raw28155Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28155 raw28155Labels permutation152 permutation6
    _ = mixedMoment B node2548 node2548Labels := by rfl

def raw28156 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw28156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28156 raw28156Labels = mixedMoment B node2581 node2581Labels := by
  calc
    mixedMoment B raw28156 raw28156Labels = mixedMoment B raw28156step0 raw28156step0Labels := by
      have hz : ∀ j, raw28156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28156step0 = (fun i j => raw28156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28156step0 raw28156; decide +kernel
      have hl : raw28156step0Labels = raw28156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28156 raw28156Labels permutation346 hz
    mixedMoment B raw28156step0 raw28156step0Labels = mixedMoment B raw28156step1 raw28156step1Labels := by
      have ha : raw28156step1 = (fun i j => raw28156step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28156step1 raw28156step0; decide +kernel
      have hl : raw28156step1Labels = raw28156step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28156step0 raw28156step0Labels permutation32 permutation6
    _ = mixedMoment B node2581 node2581Labels := by rfl

def raw28157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw28157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw28157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28157 raw28157Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw28157 raw28157Labels = mixedMoment B raw28157step0 raw28157step0Labels := by
      have hz : ∀ j, raw28157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28157step0 = (fun i j => raw28157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28157step0 raw28157; decide +kernel
      have hl : raw28157step0Labels = raw28157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28157 raw28157Labels permutation346 hz
    mixedMoment B raw28157step0 raw28157step0Labels = mixedMoment B raw28157step1 raw28157step1Labels := by
      have ha : raw28157step1 = (fun i j => raw28157step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28157step1 raw28157step0; decide +kernel
      have hl : raw28157step1Labels = raw28157step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28157step0 raw28157step0Labels permutation146 permutation3
    _ = mixedMoment B node1422 node1422Labels := by rfl

def raw28158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28158 raw28158Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw28158 raw28158Labels = mixedMoment B raw28158step0 raw28158step0Labels := by
      have hz : ∀ j, raw28158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28158step0 = (fun i j => raw28158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28158step0 raw28158; decide +kernel
      have hl : raw28158step0Labels = raw28158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28158 raw28158Labels permutation346 hz
    mixedMoment B raw28158step0 raw28158step0Labels = mixedMoment B raw28158step1 raw28158step1Labels := by
      have ha : raw28158step1 = (fun i j => raw28158step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28158step1 raw28158step0; decide +kernel
      have hl : raw28158step1Labels = raw28158step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28158step0 raw28158step0Labels permutation32 permutation6
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw28159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28159 raw28159Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw28159 raw28159Labels = mixedMoment B raw28159step0 raw28159step0Labels := by
      have hz : ∀ j, raw28159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28159step0 = (fun i j => raw28159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28159step0 raw28159; decide +kernel
      have hl : raw28159step0Labels = raw28159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28159 raw28159Labels permutation346 hz
    mixedMoment B raw28159step0 raw28159step0Labels = mixedMoment B raw28159step1 raw28159step1Labels := by
      have ha : raw28159step1 = (fun i j => raw28159step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28159step1 raw28159step0; decide +kernel
      have hl : raw28159step1Labels = raw28159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28159step0 raw28159step0Labels permutation32 permutation6
    _ = mixedMoment B node2486 node2486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
