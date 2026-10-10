import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
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

def raw29952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29952 raw29952Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw29952 raw29952Labels = mixedMoment B raw29952step0 raw29952step0Labels := by
      have hz : ∀ j, raw29952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29952step0 = (fun i j => raw29952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29952step0 raw29952; decide +kernel
      have hl : raw29952step0Labels = raw29952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29952 raw29952Labels permutation434 hz
    mixedMoment B raw29952step0 raw29952step0Labels = mixedMoment B raw29952step1 raw29952step1Labels := by
      have ha : raw29952step1 = (fun i j => raw29952step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29952step1 raw29952step0; decide +kernel
      have hl : raw29952step1Labels = raw29952step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29952step0 raw29952step0Labels permutation33 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw29953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29953step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29953step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29953 raw29953Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw29953 raw29953Labels = mixedMoment B raw29953step0 raw29953step0Labels := by
      have hz : ∀ j, raw29953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29953step0 = (fun i j => raw29953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29953step0 raw29953; decide +kernel
      have hl : raw29953step0Labels = raw29953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29953 raw29953Labels permutation346 hz
    mixedMoment B raw29953step0 raw29953step0Labels = mixedMoment B raw29953step1 raw29953step1Labels := by
      have ha : raw29953step1 = (fun i j => raw29953step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29953step1 raw29953step0; decide +kernel
      have hl : raw29953step1Labels = raw29953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29953step0 raw29953step0Labels permutation33 permutation3
    mixedMoment B raw29953step1 raw29953step1Labels = mixedMoment B raw29953step2 raw29953step2Labels := by
      have ha : raw29953step2 = raw29953step1 := by apply Matrix.ext; unfold raw29953step2 raw29953step1; decide +kernel
      have hl : raw29953step1Labels = labelEmbedding6 ∘ raw29953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29953step1 raw29953step1Labels raw29953step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw29954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29954 raw29954Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw29954 raw29954Labels = mixedMoment B raw29954step0 raw29954step0Labels := by
      have hz : ∀ j, raw29954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29954step0 = (fun i j => raw29954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29954step0 raw29954; decide +kernel
      have hl : raw29954step0Labels = raw29954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29954 raw29954Labels permutation346 hz
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw29955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29955 raw29955Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw29955 raw29955Labels = mixedMoment B raw29955step0 raw29955step0Labels := by
      have ha : raw29955step0 = (fun i j => raw29955 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29955step0 raw29955; decide +kernel
      have hl : raw29955step0Labels = raw29955Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29955 raw29955Labels permutation176 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw29956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29956 raw29956Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw29956 raw29956Labels = mixedMoment B raw29956step0 raw29956step0Labels := by
      have hz : ∀ j, raw29956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29956step0 = (fun i j => raw29956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29956step0 raw29956; decide +kernel
      have hl : raw29956step0Labels = raw29956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29956 raw29956Labels permutation346 hz
    mixedMoment B raw29956step0 raw29956step0Labels = mixedMoment B raw29956step1 raw29956step1Labels := by
      have ha : raw29956step1 = (fun i j => raw29956step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29956step1 raw29956step0; decide +kernel
      have hl : raw29956step1Labels = raw29956step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29956step0 raw29956step0Labels permutation33 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw29957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw29957step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29957step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw29957step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29957 raw29957Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw29957 raw29957Labels = mixedMoment B raw29957step0 raw29957step0Labels := by
      have hz : ∀ j, raw29957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29957step0 = (fun i j => raw29957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29957step0 raw29957; decide +kernel
      have hl : raw29957step0Labels = raw29957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29957 raw29957Labels permutation434 hz
    mixedMoment B raw29957step0 raw29957step0Labels = mixedMoment B raw29957step1 raw29957step1Labels := by
      have hz : ∀ j, raw29957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29957step1 = (fun i j => raw29957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29957step1 raw29957step0; decide +kernel
      have hl : raw29957step1Labels = raw29957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29957step0 raw29957step0Labels permutation80 hz
    mixedMoment B raw29957step1 raw29957step1Labels = mixedMoment B raw29957step2 raw29957step2Labels := by
      have ha : raw29957step2 = (fun i j => raw29957step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29957step2 raw29957step1; decide +kernel
      have hl : raw29957step2Labels = raw29957step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29957step1 raw29957step1Labels permutation9 permutation3
    mixedMoment B raw29957step2 raw29957step2Labels = mixedMoment B raw29957step3 raw29957step3Labels := by
      have ha : raw29957step3 = raw29957step2 := by apply Matrix.ext; unfold raw29957step3 raw29957step2; decide +kernel
      have hl : raw29957step2Labels = labelEmbedding6 ∘ raw29957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29957step2 raw29957step2Labels raw29957step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

def raw29958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw29958step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29958step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29958step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29958step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29958 raw29958Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw29958 raw29958Labels = mixedMoment B raw29958step0 raw29958step0Labels := by
      have hz : ∀ j, raw29958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29958step0 = (fun i j => raw29958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29958step0 raw29958; decide +kernel
      have hl : raw29958step0Labels = raw29958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29958 raw29958Labels permutation434 hz
    mixedMoment B raw29958step0 raw29958step0Labels = mixedMoment B raw29958step1 raw29958step1Labels := by
      have hz : ∀ j, raw29958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29958step1 = (fun i j => raw29958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29958step1 raw29958step0; decide +kernel
      have hl : raw29958step1Labels = raw29958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29958step0 raw29958step0Labels permutation80 hz
    mixedMoment B raw29958step1 raw29958step1Labels = mixedMoment B raw29958step2 raw29958step2Labels := by
      have ha : raw29958step2 = (fun i j => raw29958step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29958step2 raw29958step1; decide +kernel
      have hl : raw29958step2Labels = raw29958step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29958step1 raw29958step1Labels permutation25 permutation3
    mixedMoment B raw29958step2 raw29958step2Labels = mixedMoment B raw29958step3 raw29958step3Labels := by
      have ha : raw29958step3 = -raw29958step2 := by apply Matrix.ext; change ∀ i j, raw29958step3 i j = -(raw29958step2 i j); unfold raw29958step3 raw29958step2; decide +kernel
      have hl : raw29958step3Labels = raw29958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29958step3 raw29958step3Labels = mixedMoment B raw29958step4 raw29958step4Labels := by
      have ha : raw29958step4 = raw29958step3 := by apply Matrix.ext; unfold raw29958step4 raw29958step3; decide +kernel
      have hl : raw29958step3Labels = labelEmbedding6 ∘ raw29958step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29958step3 raw29958step3Labels raw29958step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

def raw29959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29959step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29959 raw29959Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw29959 raw29959Labels = mixedMoment B raw29959step0 raw29959step0Labels := by
      have hz : ∀ j, raw29959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29959step0 = (fun i j => raw29959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29959step0 raw29959; decide +kernel
      have hl : raw29959step0Labels = raw29959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29959 raw29959Labels permutation434 hz
    mixedMoment B raw29959step0 raw29959step0Labels = mixedMoment B raw29959step1 raw29959step1Labels := by
      have ha : raw29959step1 = (fun i j => raw29959step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29959step1 raw29959step0; decide +kernel
      have hl : raw29959step1Labels = raw29959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29959step0 raw29959step0Labels permutation127 permutation3
    mixedMoment B raw29959step1 raw29959step1Labels = mixedMoment B raw29959step2 raw29959step2Labels := by
      have ha : raw29959step2 = -raw29959step1 := by apply Matrix.ext; change ∀ i j, raw29959step2 i j = -(raw29959step1 i j); unfold raw29959step2 raw29959step1; decide +kernel
      have hl : raw29959step2Labels = raw29959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29959step2 raw29959step2Labels = mixedMoment B raw29959step3 raw29959step3Labels := by
      have ha : raw29959step3 = raw29959step2 := by apply Matrix.ext; unfold raw29959step3 raw29959step2; decide +kernel
      have hl : raw29959step2Labels = labelEmbedding6 ∘ raw29959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29959step2 raw29959step2Labels raw29959step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw29960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29960step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29960step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29960step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29960 raw29960Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw29960 raw29960Labels = mixedMoment B raw29960step0 raw29960step0Labels := by
      have hz : ∀ j, raw29960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29960step0 = (fun i j => raw29960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29960step0 raw29960; decide +kernel
      have hl : raw29960step0Labels = raw29960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29960 raw29960Labels permutation346 hz
    mixedMoment B raw29960step0 raw29960step0Labels = mixedMoment B raw29960step1 raw29960step1Labels := by
      have ha : raw29960step1 = (fun i j => raw29960step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29960step1 raw29960step0; decide +kernel
      have hl : raw29960step1Labels = raw29960step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29960step0 raw29960step0Labels permutation127 permutation3
    mixedMoment B raw29960step1 raw29960step1Labels = mixedMoment B raw29960step2 raw29960step2Labels := by
      have ha : raw29960step2 = -raw29960step1 := by apply Matrix.ext; change ∀ i j, raw29960step2 i j = -(raw29960step1 i j); unfold raw29960step2 raw29960step1; decide +kernel
      have hl : raw29960step2Labels = raw29960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29960step2 raw29960step2Labels = mixedMoment B raw29960step3 raw29960step3Labels := by
      have ha : raw29960step3 = raw29960step2 := by apply Matrix.ext; unfold raw29960step3 raw29960step2; decide +kernel
      have hl : raw29960step2Labels = labelEmbedding6 ∘ raw29960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29960step2 raw29960step2Labels raw29960step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw29961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw29961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw29961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29961step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29961step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29961step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29961step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29961 raw29961Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw29961 raw29961Labels = mixedMoment B raw29961step0 raw29961step0Labels := by
      have hz : ∀ j, raw29961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29961step0 = (fun i j => raw29961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29961step0 raw29961; decide +kernel
      have hl : raw29961step0Labels = raw29961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29961 raw29961Labels permutation434 hz
    mixedMoment B raw29961step0 raw29961step0Labels = mixedMoment B raw29961step1 raw29961step1Labels := by
      have hz : ∀ j, raw29961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29961step1 = (fun i j => raw29961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29961step1 raw29961step0; decide +kernel
      have hl : raw29961step1Labels = raw29961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29961step0 raw29961step0Labels permutation80 hz
    mixedMoment B raw29961step1 raw29961step1Labels = mixedMoment B raw29961step2 raw29961step2Labels := by
      have ha : raw29961step2 = (fun i j => raw29961step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29961step2 raw29961step1; decide +kernel
      have hl : raw29961step2Labels = raw29961step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29961step1 raw29961step1Labels permutation25 permutation3
    mixedMoment B raw29961step2 raw29961step2Labels = mixedMoment B raw29961step3 raw29961step3Labels := by
      have ha : raw29961step3 = -raw29961step2 := by apply Matrix.ext; change ∀ i j, raw29961step3 i j = -(raw29961step2 i j); unfold raw29961step3 raw29961step2; decide +kernel
      have hl : raw29961step3Labels = raw29961step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29961step3 raw29961step3Labels = mixedMoment B raw29961step4 raw29961step4Labels := by
      have ha : raw29961step4 = raw29961step3 := by apply Matrix.ext; unfold raw29961step4 raw29961step3; decide +kernel
      have hl : raw29961step3Labels = labelEmbedding6 ∘ raw29961step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29961step3 raw29961step3Labels raw29961step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw29962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29962 raw29962Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw29962 raw29962Labels = mixedMoment B raw29962step0 raw29962step0Labels := by
      have hz : ∀ j, raw29962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29962step0 = (fun i j => raw29962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29962step0 raw29962; decide +kernel
      have hl : raw29962step0Labels = raw29962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29962 raw29962Labels permutation434 hz
    mixedMoment B raw29962step0 raw29962step0Labels = mixedMoment B raw29962step1 raw29962step1Labels := by
      have hz : ∀ j, raw29962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29962step1 = (fun i j => raw29962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29962step1 raw29962step0; decide +kernel
      have hl : raw29962step1Labels = raw29962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29962step0 raw29962step0Labels permutation80 hz
    mixedMoment B raw29962step1 raw29962step1Labels = mixedMoment B raw29962step2 raw29962step2Labels := by
      have ha : raw29962step2 = (fun i j => raw29962step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29962step2 raw29962step1; decide +kernel
      have hl : raw29962step2Labels = raw29962step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29962step1 raw29962step1Labels permutation9 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw29963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29963 raw29963Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw29963 raw29963Labels = mixedMoment B raw29963step0 raw29963step0Labels := by
      have hz : ∀ j, raw29963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29963step0 = (fun i j => raw29963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29963step0 raw29963; decide +kernel
      have hl : raw29963step0Labels = raw29963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29963 raw29963Labels permutation434 hz
    mixedMoment B raw29963step0 raw29963step0Labels = mixedMoment B raw29963step1 raw29963step1Labels := by
      have ha : raw29963step1 = (fun i j => raw29963step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29963step1 raw29963step0; decide +kernel
      have hl : raw29963step1Labels = raw29963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29963step0 raw29963step0Labels permutation39 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw29964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29964 raw29964Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw29964 raw29964Labels = mixedMoment B raw29964step0 raw29964step0Labels := by
      have hz : ∀ j, raw29964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29964step0 = (fun i j => raw29964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29964step0 raw29964; decide +kernel
      have hl : raw29964step0Labels = raw29964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29964 raw29964Labels permutation346 hz
    mixedMoment B raw29964step0 raw29964step0Labels = mixedMoment B raw29964step1 raw29964step1Labels := by
      have ha : raw29964step1 = (fun i j => raw29964step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29964step1 raw29964step0; decide +kernel
      have hl : raw29964step1Labels = raw29964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29964step0 raw29964step0Labels permutation39 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw29965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw29965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29965 raw29965Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw29965 raw29965Labels = mixedMoment B raw29965step0 raw29965step0Labels := by
      have hz : ∀ j, raw29965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29965step0 = (fun i j => raw29965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29965step0 raw29965; decide +kernel
      have hl : raw29965step0Labels = raw29965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29965 raw29965Labels permutation434 hz
    mixedMoment B raw29965step0 raw29965step0Labels = mixedMoment B raw29965step1 raw29965step1Labels := by
      have hz : ∀ j, raw29965step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29965step1 = (fun i j => raw29965step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29965step1 raw29965step0; decide +kernel
      have hl : raw29965step1Labels = raw29965step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29965step0 raw29965step0Labels permutation80 hz
    mixedMoment B raw29965step1 raw29965step1Labels = mixedMoment B raw29965step2 raw29965step2Labels := by
      have ha : raw29965step2 = (fun i j => raw29965step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29965step2 raw29965step1; decide +kernel
      have hl : raw29965step2Labels = raw29965step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29965step1 raw29965step1Labels permutation9 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw29966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29966 raw29966Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw29966 raw29966Labels = mixedMoment B raw29966step0 raw29966step0Labels := by
      have hz : ∀ j, raw29966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29966step0 = (fun i j => raw29966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29966step0 raw29966; decide +kernel
      have hl : raw29966step0Labels = raw29966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29966 raw29966Labels permutation434 hz
    mixedMoment B raw29966step0 raw29966step0Labels = mixedMoment B raw29966step1 raw29966step1Labels := by
      have ha : raw29966step1 = (fun i j => raw29966step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29966step1 raw29966step0; decide +kernel
      have hl : raw29966step1Labels = raw29966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29966step0 raw29966step0Labels permutation33 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw29967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29967 raw29967Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw29967 raw29967Labels = mixedMoment B raw29967step0 raw29967step0Labels := by
      have hz : ∀ j, raw29967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29967step0 = (fun i j => raw29967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29967step0 raw29967; decide +kernel
      have hl : raw29967step0Labels = raw29967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29967 raw29967Labels permutation434 hz
    mixedMoment B raw29967step0 raw29967step0Labels = mixedMoment B raw29967step1 raw29967step1Labels := by
      have ha : raw29967step1 = (fun i j => raw29967step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29967step1 raw29967step0; decide +kernel
      have hl : raw29967step1Labels = raw29967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29967step0 raw29967step0Labels permutation33 permutation3
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw29968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29968 raw29968Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw29968 raw29968Labels = mixedMoment B raw29968step0 raw29968step0Labels := by
      have ha : raw29968step0 = (fun i j => raw29968 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29968step0 raw29968; decide +kernel
      have hl : raw29968step0Labels = raw29968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29968 raw29968Labels permutation159 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw29969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29969 raw29969Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw29969 raw29969Labels = mixedMoment B raw29969step0 raw29969step0Labels := by
      have hz : ∀ j, raw29969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29969step0 = (fun i j => raw29969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29969step0 raw29969; decide +kernel
      have hl : raw29969step0Labels = raw29969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29969 raw29969Labels permutation434 hz
    mixedMoment B raw29969step0 raw29969step0Labels = mixedMoment B raw29969step1 raw29969step1Labels := by
      have ha : raw29969step1 = (fun i j => raw29969step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29969step1 raw29969step0; decide +kernel
      have hl : raw29969step1Labels = raw29969step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29969step0 raw29969step0Labels permutation36 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw29970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29970 raw29970Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw29970 raw29970Labels = mixedMoment B raw29970step0 raw29970step0Labels := by
      have hz : ∀ j, raw29970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29970step0 = (fun i j => raw29970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29970step0 raw29970; decide +kernel
      have hl : raw29970step0Labels = raw29970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29970 raw29970Labels permutation346 hz
    mixedMoment B raw29970step0 raw29970step0Labels = mixedMoment B raw29970step1 raw29970step1Labels := by
      have ha : raw29970step1 = (fun i j => raw29970step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29970step1 raw29970step0; decide +kernel
      have hl : raw29970step1Labels = raw29970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29970step0 raw29970step0Labels permutation33 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw29971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29971 raw29971Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw29971 raw29971Labels = mixedMoment B raw29971step0 raw29971step0Labels := by
      have hz : ∀ j, raw29971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29971step0 = (fun i j => raw29971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29971step0 raw29971; decide +kernel
      have hl : raw29971step0Labels = raw29971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29971 raw29971Labels permutation346 hz
    mixedMoment B raw29971step0 raw29971step0Labels = mixedMoment B raw29971step1 raw29971step1Labels := by
      have ha : raw29971step1 = (fun i j => raw29971step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29971step1 raw29971step0; decide +kernel
      have hl : raw29971step1Labels = raw29971step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29971step0 raw29971step0Labels permutation33 permutation3
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw29972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29972 raw29972Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw29972 raw29972Labels = mixedMoment B raw29972step0 raw29972step0Labels := by
      have ha : raw29972step0 = (fun i j => raw29972 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29972step0 raw29972; decide +kernel
      have hl : raw29972step0Labels = raw29972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29972 raw29972Labels permutation153 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw29973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw29973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29973 raw29973Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw29973 raw29973Labels = mixedMoment B raw29973step0 raw29973step0Labels := by
      have hz : ∀ j, raw29973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29973step0 = (fun i j => raw29973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29973step0 raw29973; decide +kernel
      have hl : raw29973step0Labels = raw29973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29973 raw29973Labels permutation346 hz
    mixedMoment B raw29973step0 raw29973step0Labels = mixedMoment B raw29973step1 raw29973step1Labels := by
      have ha : raw29973step1 = (fun i j => raw29973step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29973step1 raw29973step0; decide +kernel
      have hl : raw29973step1Labels = raw29973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29973step0 raw29973step0Labels permutation36 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw29974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29974step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29974step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw29974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29974 raw29974Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw29974 raw29974Labels = mixedMoment B raw29974step0 raw29974step0Labels := by
      have hz : ∀ j, raw29974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29974step0 = (fun i j => raw29974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29974step0 raw29974; decide +kernel
      have hl : raw29974step0Labels = raw29974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29974 raw29974Labels permutation434 hz
    mixedMoment B raw29974step0 raw29974step0Labels = mixedMoment B raw29974step1 raw29974step1Labels := by
      have hz : ∀ j, raw29974step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29974step1 = (fun i j => raw29974step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29974step1 raw29974step0; decide +kernel
      have hl : raw29974step1Labels = raw29974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29974step0 raw29974step0Labels permutation80 hz
    mixedMoment B raw29974step1 raw29974step1Labels = mixedMoment B raw29974step2 raw29974step2Labels := by
      have ha : raw29974step2 = (fun i j => raw29974step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29974step2 raw29974step1; decide +kernel
      have hl : raw29974step2Labels = raw29974step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29974step1 raw29974step1Labels permutation9 permutation3
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw29975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29975step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw29975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29975step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29975 raw29975Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw29975 raw29975Labels = mixedMoment B raw29975step0 raw29975step0Labels := by
      have hz : ∀ j, raw29975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29975step0 = (fun i j => raw29975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29975step0 raw29975; decide +kernel
      have hl : raw29975step0Labels = raw29975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29975 raw29975Labels permutation434 hz
    mixedMoment B raw29975step0 raw29975step0Labels = mixedMoment B raw29975step1 raw29975step1Labels := by
      have hz : ∀ j, raw29975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29975step1 = (fun i j => raw29975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29975step1 raw29975step0; decide +kernel
      have hl : raw29975step1Labels = raw29975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29975step0 raw29975step0Labels permutation80 hz
    mixedMoment B raw29975step1 raw29975step1Labels = mixedMoment B raw29975step2 raw29975step2Labels := by
      have ha : raw29975step2 = (fun i j => raw29975step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29975step2 raw29975step1; decide +kernel
      have hl : raw29975step2Labels = raw29975step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29975step1 raw29975step1Labels permutation25 permutation3
    mixedMoment B raw29975step2 raw29975step2Labels = mixedMoment B raw29975step3 raw29975step3Labels := by
      have ha : raw29975step3 = -raw29975step2 := by apply Matrix.ext; change ∀ i j, raw29975step3 i j = -(raw29975step2 i j); unfold raw29975step3 raw29975step2; decide +kernel
      have hl : raw29975step3Labels = raw29975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1783 node1783Labels := by rfl

def raw29976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29976 raw29976Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw29976 raw29976Labels = mixedMoment B raw29976step0 raw29976step0Labels := by
      have hz : ∀ j, raw29976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29976step0 = (fun i j => raw29976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29976step0 raw29976; decide +kernel
      have hl : raw29976step0Labels = raw29976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29976 raw29976Labels permutation434 hz
    mixedMoment B raw29976step0 raw29976step0Labels = mixedMoment B raw29976step1 raw29976step1Labels := by
      have ha : raw29976step1 = (fun i j => raw29976step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29976step1 raw29976step0; decide +kernel
      have hl : raw29976step1Labels = raw29976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29976step0 raw29976step0Labels permutation127 permutation3
    mixedMoment B raw29976step1 raw29976step1Labels = mixedMoment B raw29976step2 raw29976step2Labels := by
      have ha : raw29976step2 = -raw29976step1 := by apply Matrix.ext; change ∀ i j, raw29976step2 i j = -(raw29976step1 i j); unfold raw29976step2 raw29976step1; decide +kernel
      have hl : raw29976step2Labels = raw29976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw29977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![3, -3, 0], ![2, -1, -1]]
def raw29977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29977 raw29977Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw29977 raw29977Labels = mixedMoment B raw29977step0 raw29977step0Labels := by
      have hz : ∀ j, raw29977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29977step0 = (fun i j => raw29977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29977step0 raw29977; decide +kernel
      have hl : raw29977step0Labels = raw29977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29977 raw29977Labels permutation346 hz
    mixedMoment B raw29977step0 raw29977step0Labels = mixedMoment B raw29977step1 raw29977step1Labels := by
      have ha : raw29977step1 = (fun i j => raw29977step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29977step1 raw29977step0; decide +kernel
      have hl : raw29977step1Labels = raw29977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29977step0 raw29977step0Labels permutation127 permutation3
    mixedMoment B raw29977step1 raw29977step1Labels = mixedMoment B raw29977step2 raw29977step2Labels := by
      have ha : raw29977step2 = -raw29977step1 := by apply Matrix.ext; change ∀ i j, raw29977step2 i j = -(raw29977step1 i j); unfold raw29977step2 raw29977step1; decide +kernel
      have hl : raw29977step2Labels = raw29977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw29978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw29978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0], ![1, 0, -1]]
def raw29978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29978step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29978step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29978 raw29978Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw29978 raw29978Labels = mixedMoment B raw29978step0 raw29978step0Labels := by
      have hz : ∀ j, raw29978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29978step0 = (fun i j => raw29978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29978step0 raw29978; decide +kernel
      have hl : raw29978step0Labels = raw29978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29978 raw29978Labels permutation434 hz
    mixedMoment B raw29978step0 raw29978step0Labels = mixedMoment B raw29978step1 raw29978step1Labels := by
      have hz : ∀ j, raw29978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29978step1 = (fun i j => raw29978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29978step1 raw29978step0; decide +kernel
      have hl : raw29978step1Labels = raw29978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29978step0 raw29978step0Labels permutation80 hz
    mixedMoment B raw29978step1 raw29978step1Labels = mixedMoment B raw29978step2 raw29978step2Labels := by
      have ha : raw29978step2 = (fun i j => raw29978step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29978step2 raw29978step1; decide +kernel
      have hl : raw29978step2Labels = raw29978step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29978step1 raw29978step1Labels permutation25 permutation3
    mixedMoment B raw29978step2 raw29978step2Labels = mixedMoment B raw29978step3 raw29978step3Labels := by
      have ha : raw29978step3 = -raw29978step2 := by apply Matrix.ext; change ∀ i j, raw29978step3 i j = -(raw29978step2 i j); unfold raw29978step3 raw29978step2; decide +kernel
      have hl : raw29978step3Labels = raw29978step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw29979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw29979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29979 raw29979Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw29979 raw29979Labels = mixedMoment B raw29979step0 raw29979step0Labels := by
      have hz : ∀ j, raw29979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29979step0 = (fun i j => raw29979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29979step0 raw29979; decide +kernel
      have hl : raw29979step0Labels = raw29979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29979 raw29979Labels permutation434 hz
    mixedMoment B raw29979step0 raw29979step0Labels = mixedMoment B raw29979step1 raw29979step1Labels := by
      have hz : ∀ j, raw29979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29979step1 = (fun i j => raw29979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29979step1 raw29979step0; decide +kernel
      have hl : raw29979step1Labels = raw29979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29979step0 raw29979step0Labels permutation80 hz
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw29980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29980step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29980 raw29980Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw29980 raw29980Labels = mixedMoment B raw29980step0 raw29980step0Labels := by
      have hz : ∀ j, raw29980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29980step0 = (fun i j => raw29980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29980step0 raw29980; decide +kernel
      have hl : raw29980step0Labels = raw29980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29980 raw29980Labels permutation434 hz
    mixedMoment B raw29980step0 raw29980step0Labels = mixedMoment B raw29980step1 raw29980step1Labels := by
      have hz : ∀ j, raw29980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29980step1 = (fun i j => raw29980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29980step1 raw29980step0; decide +kernel
      have hl : raw29980step1Labels = raw29980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29980step0 raw29980step0Labels permutation80 hz
    mixedMoment B raw29980step1 raw29980step1Labels = mixedMoment B raw29980step2 raw29980step2Labels := by
      have ha : raw29980step2 = (fun i j => raw29980step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29980step2 raw29980step1; decide +kernel
      have hl : raw29980step2Labels = raw29980step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29980step1 raw29980step1Labels permutation8 permutation3
    mixedMoment B raw29980step2 raw29980step2Labels = mixedMoment B raw29980step3 raw29980step3Labels := by
      have ha : raw29980step3 = raw29980step2 := by apply Matrix.ext; unfold raw29980step3 raw29980step2; decide +kernel
      have hl : raw29980step2Labels = labelEmbedding6 ∘ raw29980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29980step2 raw29980step2Labels raw29980step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw29981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29981 raw29981Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw29981 raw29981Labels = mixedMoment B raw29981step0 raw29981step0Labels := by
      have hz : ∀ j, raw29981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29981step0 = (fun i j => raw29981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29981step0 raw29981; decide +kernel
      have hl : raw29981step0Labels = raw29981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29981 raw29981Labels permutation434 hz
    mixedMoment B raw29981step0 raw29981step0Labels = mixedMoment B raw29981step1 raw29981step1Labels := by
      have ha : raw29981step1 = (fun i j => raw29981step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29981step1 raw29981step0; decide +kernel
      have hl : raw29981step1Labels = raw29981step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29981step0 raw29981step0Labels permutation38 permutation3
    mixedMoment B raw29981step1 raw29981step1Labels = mixedMoment B raw29981step2 raw29981step2Labels := by
      have ha : raw29981step2 = raw29981step1 := by apply Matrix.ext; unfold raw29981step2 raw29981step1; decide +kernel
      have hl : raw29981step1Labels = labelEmbedding6 ∘ raw29981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29981step1 raw29981step1Labels raw29981step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw29982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29982 raw29982Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw29982 raw29982Labels = mixedMoment B raw29982step0 raw29982step0Labels := by
      have hz : ∀ j, raw29982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29982step0 = (fun i j => raw29982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29982step0 raw29982; decide +kernel
      have hl : raw29982step0Labels = raw29982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29982 raw29982Labels permutation346 hz
    mixedMoment B raw29982step0 raw29982step0Labels = mixedMoment B raw29982step1 raw29982step1Labels := by
      have ha : raw29982step1 = (fun i j => raw29982step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29982step1 raw29982step0; decide +kernel
      have hl : raw29982step1Labels = raw29982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29982step0 raw29982step0Labels permutation38 permutation3
    mixedMoment B raw29982step1 raw29982step1Labels = mixedMoment B raw29982step2 raw29982step2Labels := by
      have ha : raw29982step2 = raw29982step1 := by apply Matrix.ext; unfold raw29982step2 raw29982step1; decide +kernel
      have hl : raw29982step1Labels = labelEmbedding6 ∘ raw29982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29982step1 raw29982step1Labels raw29982step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw29983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw29983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29983 raw29983Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw29983 raw29983Labels = mixedMoment B raw29983step0 raw29983step0Labels := by
      have hz : ∀ j, raw29983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29983step0 = (fun i j => raw29983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29983step0 raw29983; decide +kernel
      have hl : raw29983step0Labels = raw29983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29983 raw29983Labels permutation434 hz
    mixedMoment B raw29983step0 raw29983step0Labels = mixedMoment B raw29983step1 raw29983step1Labels := by
      have hz : ∀ j, raw29983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29983step1 = (fun i j => raw29983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29983step1 raw29983step0; decide +kernel
      have hl : raw29983step1Labels = raw29983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29983step0 raw29983step0Labels permutation80 hz
    mixedMoment B raw29983step1 raw29983step1Labels = mixedMoment B raw29983step2 raw29983step2Labels := by
      have ha : raw29983step2 = (fun i j => raw29983step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29983step2 raw29983step1; decide +kernel
      have hl : raw29983step2Labels = raw29983step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29983step1 raw29983step1Labels permutation9 permutation3
    mixedMoment B raw29983step2 raw29983step2Labels = mixedMoment B raw29983step3 raw29983step3Labels := by
      have ha : raw29983step3 = raw29983step2 := by apply Matrix.ext; unfold raw29983step3 raw29983step2; decide +kernel
      have hl : raw29983step2Labels = labelEmbedding6 ∘ raw29983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29983step2 raw29983step2Labels raw29983step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw29984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29984 raw29984Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw29984 raw29984Labels = mixedMoment B raw29984step0 raw29984step0Labels := by
      have hz : ∀ j, raw29984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29984step0 = (fun i j => raw29984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29984step0 raw29984; decide +kernel
      have hl : raw29984step0Labels = raw29984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29984 raw29984Labels permutation434 hz
    mixedMoment B raw29984step0 raw29984step0Labels = mixedMoment B raw29984step1 raw29984step1Labels := by
      have ha : raw29984step1 = (fun i j => raw29984step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29984step1 raw29984step0; decide +kernel
      have hl : raw29984step1Labels = raw29984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29984step0 raw29984step0Labels permutation32 permutation3
    mixedMoment B raw29984step1 raw29984step1Labels = mixedMoment B raw29984step2 raw29984step2Labels := by
      have ha : raw29984step2 = raw29984step1 := by apply Matrix.ext; unfold raw29984step2 raw29984step1; decide +kernel
      have hl : raw29984step1Labels = labelEmbedding6 ∘ raw29984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29984step1 raw29984step1Labels raw29984step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw29985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29985 raw29985Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw29985 raw29985Labels = mixedMoment B raw29985step0 raw29985step0Labels := by
      have hz : ∀ j, raw29985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29985step0 = (fun i j => raw29985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29985step0 raw29985; decide +kernel
      have hl : raw29985step0Labels = raw29985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29985 raw29985Labels permutation434 hz
    mixedMoment B raw29985step0 raw29985step0Labels = mixedMoment B raw29985step1 raw29985step1Labels := by
      have ha : raw29985step1 = (fun i j => raw29985step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29985step1 raw29985step0; decide +kernel
      have hl : raw29985step1Labels = raw29985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29985step0 raw29985step0Labels permutation32 permutation3
    mixedMoment B raw29985step1 raw29985step1Labels = mixedMoment B raw29985step2 raw29985step2Labels := by
      have ha : raw29985step2 = raw29985step1 := by apply Matrix.ext; unfold raw29985step2 raw29985step1; decide +kernel
      have hl : raw29985step1Labels = labelEmbedding6 ∘ raw29985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29985step1 raw29985step1Labels raw29985step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw29986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29986 raw29986Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw29986 raw29986Labels = mixedMoment B raw29986step0 raw29986step0Labels := by
      have ha : raw29986step0 = (fun i j => raw29986 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29986step0 raw29986; decide +kernel
      have hl : raw29986step0Labels = raw29986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29986 raw29986Labels permutation200 permutation3
    mixedMoment B raw29986step0 raw29986step0Labels = mixedMoment B raw29986step1 raw29986step1Labels := by
      have ha : raw29986step1 = raw29986step0 := by apply Matrix.ext; unfold raw29986step1 raw29986step0; decide +kernel
      have hl : raw29986step0Labels = labelEmbedding6 ∘ raw29986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29986step0 raw29986step0Labels raw29986step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw29987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29987 raw29987Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw29987 raw29987Labels = mixedMoment B raw29987step0 raw29987step0Labels := by
      have hz : ∀ j, raw29987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29987step0 = (fun i j => raw29987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29987step0 raw29987; decide +kernel
      have hl : raw29987step0Labels = raw29987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29987 raw29987Labels permutation434 hz
    mixedMoment B raw29987step0 raw29987step0Labels = mixedMoment B raw29987step1 raw29987step1Labels := by
      have ha : raw29987step1 = (fun i j => raw29987step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29987step1 raw29987step0; decide +kernel
      have hl : raw29987step1Labels = raw29987step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29987step0 raw29987step0Labels permutation36 permutation3
    mixedMoment B raw29987step1 raw29987step1Labels = mixedMoment B raw29987step2 raw29987step2Labels := by
      have ha : raw29987step2 = raw29987step1 := by apply Matrix.ext; unfold raw29987step2 raw29987step1; decide +kernel
      have hl : raw29987step1Labels = labelEmbedding6 ∘ raw29987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29987step1 raw29987step1Labels raw29987step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw29988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29988 raw29988Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw29988 raw29988Labels = mixedMoment B raw29988step0 raw29988step0Labels := by
      have hz : ∀ j, raw29988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29988step0 = (fun i j => raw29988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29988step0 raw29988; decide +kernel
      have hl : raw29988step0Labels = raw29988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29988 raw29988Labels permutation346 hz
    mixedMoment B raw29988step0 raw29988step0Labels = mixedMoment B raw29988step1 raw29988step1Labels := by
      have ha : raw29988step1 = (fun i j => raw29988step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29988step1 raw29988step0; decide +kernel
      have hl : raw29988step1Labels = raw29988step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29988step0 raw29988step0Labels permutation32 permutation3
    mixedMoment B raw29988step1 raw29988step1Labels = mixedMoment B raw29988step2 raw29988step2Labels := by
      have ha : raw29988step2 = raw29988step1 := by apply Matrix.ext; unfold raw29988step2 raw29988step1; decide +kernel
      have hl : raw29988step1Labels = labelEmbedding6 ∘ raw29988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29988step1 raw29988step1Labels raw29988step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw29989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29989 raw29989Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw29989 raw29989Labels = mixedMoment B raw29989step0 raw29989step0Labels := by
      have hz : ∀ j, raw29989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29989step0 = (fun i j => raw29989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29989step0 raw29989; decide +kernel
      have hl : raw29989step0Labels = raw29989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29989 raw29989Labels permutation346 hz
    mixedMoment B raw29989step0 raw29989step0Labels = mixedMoment B raw29989step1 raw29989step1Labels := by
      have ha : raw29989step1 = (fun i j => raw29989step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29989step1 raw29989step0; decide +kernel
      have hl : raw29989step1Labels = raw29989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29989step0 raw29989step0Labels permutation32 permutation3
    mixedMoment B raw29989step1 raw29989step1Labels = mixedMoment B raw29989step2 raw29989step2Labels := by
      have ha : raw29989step2 = raw29989step1 := by apply Matrix.ext; unfold raw29989step2 raw29989step1; decide +kernel
      have hl : raw29989step1Labels = labelEmbedding6 ∘ raw29989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29989step1 raw29989step1Labels raw29989step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw29990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29990 raw29990Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw29990 raw29990Labels = mixedMoment B raw29990step0 raw29990step0Labels := by
      have ha : raw29990step0 = (fun i j => raw29990 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29990step0 raw29990; decide +kernel
      have hl : raw29990step0Labels = raw29990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29990 raw29990Labels permutation176 permutation3
    mixedMoment B raw29990step0 raw29990step0Labels = mixedMoment B raw29990step1 raw29990step1Labels := by
      have ha : raw29990step1 = raw29990step0 := by apply Matrix.ext; unfold raw29990step1 raw29990step0; decide +kernel
      have hl : raw29990step0Labels = labelEmbedding6 ∘ raw29990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29990step0 raw29990step0Labels raw29990step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw29991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw29991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29991 raw29991Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw29991 raw29991Labels = mixedMoment B raw29991step0 raw29991step0Labels := by
      have hz : ∀ j, raw29991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29991step0 = (fun i j => raw29991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29991step0 raw29991; decide +kernel
      have hl : raw29991step0Labels = raw29991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29991 raw29991Labels permutation346 hz
    mixedMoment B raw29991step0 raw29991step0Labels = mixedMoment B raw29991step1 raw29991step1Labels := by
      have ha : raw29991step1 = (fun i j => raw29991step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29991step1 raw29991step0; decide +kernel
      have hl : raw29991step1Labels = raw29991step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29991step0 raw29991step0Labels permutation36 permutation3
    mixedMoment B raw29991step1 raw29991step1Labels = mixedMoment B raw29991step2 raw29991step2Labels := by
      have ha : raw29991step2 = raw29991step1 := by apply Matrix.ext; unfold raw29991step2 raw29991step1; decide +kernel
      have hl : raw29991step1Labels = labelEmbedding6 ∘ raw29991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29991step1 raw29991step1Labels raw29991step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw29992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29992 raw29992Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw29992 raw29992Labels = mixedMoment B raw29992step0 raw29992step0Labels := by
      have hz : ∀ j, raw29992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29992step0 = (fun i j => raw29992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29992step0 raw29992; decide +kernel
      have hl : raw29992step0Labels = raw29992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29992 raw29992Labels permutation434 hz
    mixedMoment B raw29992step0 raw29992step0Labels = mixedMoment B raw29992step1 raw29992step1Labels := by
      have hz : ∀ j, raw29992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29992step1 = (fun i j => raw29992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29992step1 raw29992step0; decide +kernel
      have hl : raw29992step1Labels = raw29992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29992step0 raw29992step0Labels permutation80 hz
    mixedMoment B raw29992step1 raw29992step1Labels = mixedMoment B raw29992step2 raw29992step2Labels := by
      have ha : raw29992step2 = (fun i j => raw29992step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29992step2 raw29992step1; decide +kernel
      have hl : raw29992step2Labels = raw29992step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29992step1 raw29992step1Labels permutation9 permutation3
    mixedMoment B raw29992step2 raw29992step2Labels = mixedMoment B raw29992step3 raw29992step3Labels := by
      have ha : raw29992step3 = raw29992step2 := by apply Matrix.ext; unfold raw29992step3 raw29992step2; decide +kernel
      have hl : raw29992step2Labels = labelEmbedding6 ∘ raw29992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29992step2 raw29992step2Labels raw29992step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw29993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29993 raw29993Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw29993 raw29993Labels = mixedMoment B raw29993step0 raw29993step0Labels := by
      have hz : ∀ j, raw29993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29993step0 = (fun i j => raw29993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29993step0 raw29993; decide +kernel
      have hl : raw29993step0Labels = raw29993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29993 raw29993Labels permutation434 hz
    mixedMoment B raw29993step0 raw29993step0Labels = mixedMoment B raw29993step1 raw29993step1Labels := by
      have hz : ∀ j, raw29993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29993step1 = (fun i j => raw29993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29993step1 raw29993step0; decide +kernel
      have hl : raw29993step1Labels = raw29993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29993step0 raw29993step0Labels permutation80 hz
    mixedMoment B raw29993step1 raw29993step1Labels = mixedMoment B raw29993step2 raw29993step2Labels := by
      have ha : raw29993step2 = (fun i j => raw29993step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29993step2 raw29993step1; decide +kernel
      have hl : raw29993step2Labels = raw29993step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29993step1 raw29993step1Labels permutation25 permutation2
    mixedMoment B raw29993step2 raw29993step2Labels = mixedMoment B raw29993step3 raw29993step3Labels := by
      have ha : raw29993step3 = -raw29993step2 := by apply Matrix.ext; change ∀ i j, raw29993step3 i j = -(raw29993step2 i j); unfold raw29993step3 raw29993step2; decide +kernel
      have hl : raw29993step3Labels = raw29993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw29994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29994step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29994 raw29994Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw29994 raw29994Labels = mixedMoment B raw29994step0 raw29994step0Labels := by
      have hz : ∀ j, raw29994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29994step0 = (fun i j => raw29994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29994step0 raw29994; decide +kernel
      have hl : raw29994step0Labels = raw29994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29994 raw29994Labels permutation434 hz
    mixedMoment B raw29994step0 raw29994step0Labels = mixedMoment B raw29994step1 raw29994step1Labels := by
      have ha : raw29994step1 = (fun i j => raw29994step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29994step1 raw29994step0; decide +kernel
      have hl : raw29994step1Labels = raw29994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29994step0 raw29994step0Labels permutation127 permutation2
    mixedMoment B raw29994step1 raw29994step1Labels = mixedMoment B raw29994step2 raw29994step2Labels := by
      have ha : raw29994step2 = -raw29994step1 := by apply Matrix.ext; change ∀ i j, raw29994step2 i j = -(raw29994step1 i j); unfold raw29994step2 raw29994step1; decide +kernel
      have hl : raw29994step2Labels = raw29994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw29995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29995 raw29995Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw29995 raw29995Labels = mixedMoment B raw29995step0 raw29995step0Labels := by
      have hz : ∀ j, raw29995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29995step0 = (fun i j => raw29995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29995step0 raw29995; decide +kernel
      have hl : raw29995step0Labels = raw29995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29995 raw29995Labels permutation346 hz
    mixedMoment B raw29995step0 raw29995step0Labels = mixedMoment B raw29995step1 raw29995step1Labels := by
      have ha : raw29995step1 = (fun i j => raw29995step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29995step1 raw29995step0; decide +kernel
      have hl : raw29995step1Labels = raw29995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29995step0 raw29995step0Labels permutation127 permutation2
    mixedMoment B raw29995step1 raw29995step1Labels = mixedMoment B raw29995step2 raw29995step2Labels := by
      have ha : raw29995step2 = -raw29995step1 := by apply Matrix.ext; change ∀ i j, raw29995step2 i j = -(raw29995step1 i j); unfold raw29995step2 raw29995step1; decide +kernel
      have hl : raw29995step2Labels = raw29995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw29996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw29996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw29996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29996 raw29996Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw29996 raw29996Labels = mixedMoment B raw29996step0 raw29996step0Labels := by
      have hz : ∀ j, raw29996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29996step0 = (fun i j => raw29996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29996step0 raw29996; decide +kernel
      have hl : raw29996step0Labels = raw29996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29996 raw29996Labels permutation434 hz
    mixedMoment B raw29996step0 raw29996step0Labels = mixedMoment B raw29996step1 raw29996step1Labels := by
      have hz : ∀ j, raw29996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29996step1 = (fun i j => raw29996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29996step1 raw29996step0; decide +kernel
      have hl : raw29996step1Labels = raw29996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29996step0 raw29996step0Labels permutation80 hz
    mixedMoment B raw29996step1 raw29996step1Labels = mixedMoment B raw29996step2 raw29996step2Labels := by
      have ha : raw29996step2 = (fun i j => raw29996step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29996step2 raw29996step1; decide +kernel
      have hl : raw29996step2Labels = raw29996step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29996step1 raw29996step1Labels permutation25 permutation2
    mixedMoment B raw29996step2 raw29996step2Labels = mixedMoment B raw29996step3 raw29996step3Labels := by
      have ha : raw29996step3 = -raw29996step2 := by apply Matrix.ext; change ∀ i j, raw29996step3 i j = -(raw29996step2 i j); unfold raw29996step3 raw29996step2; decide +kernel
      have hl : raw29996step3Labels = raw29996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw29997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29997 raw29997Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw29997 raw29997Labels = mixedMoment B raw29997step0 raw29997step0Labels := by
      have hz : ∀ j, raw29997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29997step0 = (fun i j => raw29997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29997step0 raw29997; decide +kernel
      have hl : raw29997step0Labels = raw29997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29997 raw29997Labels permutation434 hz
    mixedMoment B raw29997step0 raw29997step0Labels = mixedMoment B raw29997step1 raw29997step1Labels := by
      have hz : ∀ j, raw29997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29997step1 = (fun i j => raw29997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29997step1 raw29997step0; decide +kernel
      have hl : raw29997step1Labels = raw29997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29997step0 raw29997step0Labels permutation80 hz
    mixedMoment B raw29997step1 raw29997step1Labels = mixedMoment B raw29997step2 raw29997step2Labels := by
      have ha : raw29997step2 = (fun i j => raw29997step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29997step2 raw29997step1; decide +kernel
      have hl : raw29997step2Labels = raw29997step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29997step1 raw29997step1Labels permutation8 permutation3
    mixedMoment B raw29997step2 raw29997step2Labels = mixedMoment B raw29997step3 raw29997step3Labels := by
      have ha : raw29997step3 = raw29997step2 := by apply Matrix.ext; unfold raw29997step3 raw29997step2; decide +kernel
      have hl : raw29997step2Labels = labelEmbedding6 ∘ raw29997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29997step2 raw29997step2Labels raw29997step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4373 node4373Labels := by rfl

def raw29998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw29998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29998 raw29998Labels = mixedMoment B node4979 node4979Labels := by
  calc
    mixedMoment B raw29998 raw29998Labels = mixedMoment B raw29998step0 raw29998step0Labels := by
      have hz : ∀ j, raw29998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29998step0 = (fun i j => raw29998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29998step0 raw29998; decide +kernel
      have hl : raw29998step0Labels = raw29998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29998 raw29998Labels permutation434 hz
    mixedMoment B raw29998step0 raw29998step0Labels = mixedMoment B raw29998step1 raw29998step1Labels := by
      have hz : ∀ j, raw29998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29998step1 = (fun i j => raw29998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29998step1 raw29998step0; decide +kernel
      have hl : raw29998step1Labels = raw29998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29998step0 raw29998step0Labels permutation80 hz
    mixedMoment B raw29998step1 raw29998step1Labels = mixedMoment B raw29998step2 raw29998step2Labels := by
      have ha : raw29998step2 = (fun i j => raw29998step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29998step2 raw29998step1; decide +kernel
      have hl : raw29998step2Labels = raw29998step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29998step1 raw29998step1Labels permutation8 permutation3
    mixedMoment B raw29998step2 raw29998step2Labels = mixedMoment B raw29998step3 raw29998step3Labels := by
      have ha : raw29998step3 = raw29998step2 := by apply Matrix.ext; unfold raw29998step3 raw29998step2; decide +kernel
      have hl : raw29998step2Labels = labelEmbedding6 ∘ raw29998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29998step2 raw29998step2Labels raw29998step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4979 node4979Labels := by rfl

def raw29999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29999step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29999step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29999step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29999 raw29999Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw29999 raw29999Labels = mixedMoment B raw29999step0 raw29999step0Labels := by
      have hz : ∀ j, raw29999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29999step0 = (fun i j => raw29999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29999step0 raw29999; decide +kernel
      have hl : raw29999step0Labels = raw29999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29999 raw29999Labels permutation434 hz
    mixedMoment B raw29999step0 raw29999step0Labels = mixedMoment B raw29999step1 raw29999step1Labels := by
      have ha : raw29999step1 = (fun i j => raw29999step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29999step1 raw29999step0; decide +kernel
      have hl : raw29999step1Labels = raw29999step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29999step0 raw29999step0Labels permutation149 permutation3
    mixedMoment B raw29999step1 raw29999step1Labels = mixedMoment B raw29999step2 raw29999step2Labels := by
      have ha : raw29999step2 = -raw29999step1 := by apply Matrix.ext; change ∀ i j, raw29999step2 i j = -(raw29999step1 i j); unfold raw29999step2 raw29999step1; decide +kernel
      have hl : raw29999step2Labels = raw29999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29999step2 raw29999step2Labels = mixedMoment B raw29999step3 raw29999step3Labels := by
      have ha : raw29999step3 = raw29999step2 := by apply Matrix.ext; unfold raw29999step3 raw29999step2; decide +kernel
      have hl : raw29999step2Labels = labelEmbedding6 ∘ raw29999step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29999step2 raw29999step2Labels raw29999step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw30000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30000 raw30000Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw30000 raw30000Labels = mixedMoment B raw30000step0 raw30000step0Labels := by
      have hz : ∀ j, raw30000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30000step0 = (fun i j => raw30000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30000step0 raw30000; decide +kernel
      have hl : raw30000step0Labels = raw30000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30000 raw30000Labels permutation346 hz
    mixedMoment B raw30000step0 raw30000step0Labels = mixedMoment B raw30000step1 raw30000step1Labels := by
      have ha : raw30000step1 = (fun i j => raw30000step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30000step1 raw30000step0; decide +kernel
      have hl : raw30000step1Labels = raw30000step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30000step0 raw30000step0Labels permutation149 permutation3
    mixedMoment B raw30000step1 raw30000step1Labels = mixedMoment B raw30000step2 raw30000step2Labels := by
      have ha : raw30000step2 = -raw30000step1 := by apply Matrix.ext; change ∀ i j, raw30000step2 i j = -(raw30000step1 i j); unfold raw30000step2 raw30000step1; decide +kernel
      have hl : raw30000step2Labels = raw30000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30000step2 raw30000step2Labels = mixedMoment B raw30000step3 raw30000step3Labels := by
      have ha : raw30000step3 = raw30000step2 := by apply Matrix.ext; unfold raw30000step3 raw30000step2; decide +kernel
      have hl : raw30000step2Labels = labelEmbedding6 ∘ raw30000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30000step2 raw30000step2Labels raw30000step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw30001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30001 raw30001Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw30001 raw30001Labels = mixedMoment B raw30001step0 raw30001step0Labels := by
      have hz : ∀ j, raw30001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30001step0 = (fun i j => raw30001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30001step0 raw30001; decide +kernel
      have hl : raw30001step0Labels = raw30001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30001 raw30001Labels permutation434 hz
    mixedMoment B raw30001step0 raw30001step0Labels = mixedMoment B raw30001step1 raw30001step1Labels := by
      have hz : ∀ j, raw30001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30001step1 = (fun i j => raw30001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30001step1 raw30001step0; decide +kernel
      have hl : raw30001step1Labels = raw30001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30001step0 raw30001step0Labels permutation80 hz
    mixedMoment B raw30001step1 raw30001step1Labels = mixedMoment B raw30001step2 raw30001step2Labels := by
      have ha : raw30001step2 = (fun i j => raw30001step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30001step2 raw30001step1; decide +kernel
      have hl : raw30001step2Labels = raw30001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30001step1 raw30001step1Labels permutation24 permutation7
    mixedMoment B raw30001step2 raw30001step2Labels = mixedMoment B raw30001step3 raw30001step3Labels := by
      have ha : raw30001step3 = raw30001step2 := by apply Matrix.ext; unfold raw30001step3 raw30001step2; decide +kernel
      have hl : raw30001step2Labels = labelEmbedding1 ∘ raw30001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30001step2 raw30001step2Labels raw30001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw30002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30002 raw30002Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw30002 raw30002Labels = mixedMoment B raw30002step0 raw30002step0Labels := by
      have hz : ∀ j, raw30002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30002step0 = (fun i j => raw30002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30002step0 raw30002; decide +kernel
      have hl : raw30002step0Labels = raw30002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30002 raw30002Labels permutation434 hz
    mixedMoment B raw30002step0 raw30002step0Labels = mixedMoment B raw30002step1 raw30002step1Labels := by
      have hz : ∀ j, raw30002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30002step1 = (fun i j => raw30002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30002step1 raw30002step0; decide +kernel
      have hl : raw30002step1Labels = raw30002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30002step0 raw30002step0Labels permutation80 hz
    mixedMoment B raw30002step1 raw30002step1Labels = mixedMoment B raw30002step2 raw30002step2Labels := by
      have ha : raw30002step2 = (fun i j => raw30002step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30002step2 raw30002step1; decide +kernel
      have hl : raw30002step2Labels = raw30002step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30002step1 raw30002step1Labels permutation11 permutation5
    mixedMoment B raw30002step2 raw30002step2Labels = mixedMoment B raw30002step3 raw30002step3Labels := by
      have ha : raw30002step3 = -raw30002step2 := by apply Matrix.ext; change ∀ i j, raw30002step3 i j = -(raw30002step2 i j); unfold raw30002step3 raw30002step2; decide +kernel
      have hl : raw30002step3Labels = raw30002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30002step3 raw30002step3Labels = mixedMoment B raw30002step4 raw30002step4Labels := by
      have ha : raw30002step4 = raw30002step3 := by apply Matrix.ext; unfold raw30002step4 raw30002step3; decide +kernel
      have hl : raw30002step3Labels = labelEmbedding1 ∘ raw30002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30002step3 raw30002step3Labels raw30002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw30003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30003 raw30003Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw30003 raw30003Labels = mixedMoment B raw30003step0 raw30003step0Labels := by
      have hz : ∀ j, raw30003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30003step0 = (fun i j => raw30003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30003step0 raw30003; decide +kernel
      have hl : raw30003step0Labels = raw30003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30003 raw30003Labels permutation434 hz
    mixedMoment B raw30003step0 raw30003step0Labels = mixedMoment B raw30003step1 raw30003step1Labels := by
      have ha : raw30003step1 = (fun i j => raw30003step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30003step1 raw30003step0; decide +kernel
      have hl : raw30003step1Labels = raw30003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30003step0 raw30003step0Labels permutation41 permutation5
    mixedMoment B raw30003step1 raw30003step1Labels = mixedMoment B raw30003step2 raw30003step2Labels := by
      have ha : raw30003step2 = -raw30003step1 := by apply Matrix.ext; change ∀ i j, raw30003step2 i j = -(raw30003step1 i j); unfold raw30003step2 raw30003step1; decide +kernel
      have hl : raw30003step2Labels = raw30003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30003step2 raw30003step2Labels = mixedMoment B raw30003step3 raw30003step3Labels := by
      have ha : raw30003step3 = raw30003step2 := by apply Matrix.ext; unfold raw30003step3 raw30003step2; decide +kernel
      have hl : raw30003step2Labels = labelEmbedding1 ∘ raw30003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30003step2 raw30003step2Labels raw30003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw30004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw30004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw30004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30004 raw30004Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw30004 raw30004Labels = mixedMoment B raw30004step0 raw30004step0Labels := by
      have hz : ∀ j, raw30004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30004step0 = (fun i j => raw30004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30004step0 raw30004; decide +kernel
      have hl : raw30004step0Labels = raw30004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30004 raw30004Labels permutation346 hz
    mixedMoment B raw30004step0 raw30004step0Labels = mixedMoment B raw30004step1 raw30004step1Labels := by
      have ha : raw30004step1 = (fun i j => raw30004step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30004step1 raw30004step0; decide +kernel
      have hl : raw30004step1Labels = raw30004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30004step0 raw30004step0Labels permutation41 permutation5
    mixedMoment B raw30004step1 raw30004step1Labels = mixedMoment B raw30004step2 raw30004step2Labels := by
      have ha : raw30004step2 = -raw30004step1 := by apply Matrix.ext; change ∀ i j, raw30004step2 i j = -(raw30004step1 i j); unfold raw30004step2 raw30004step1; decide +kernel
      have hl : raw30004step2Labels = raw30004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30004step2 raw30004step2Labels = mixedMoment B raw30004step3 raw30004step3Labels := by
      have ha : raw30004step3 = raw30004step2 := by apply Matrix.ext; unfold raw30004step3 raw30004step2; decide +kernel
      have hl : raw30004step2Labels = labelEmbedding1 ∘ raw30004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30004step2 raw30004step2Labels raw30004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw30005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30005step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw30005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30005step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw30005step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30005 raw30005Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw30005 raw30005Labels = mixedMoment B raw30005step0 raw30005step0Labels := by
      have hz : ∀ j, raw30005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30005step0 = (fun i j => raw30005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30005step0 raw30005; decide +kernel
      have hl : raw30005step0Labels = raw30005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30005 raw30005Labels permutation434 hz
    mixedMoment B raw30005step0 raw30005step0Labels = mixedMoment B raw30005step1 raw30005step1Labels := by
      have hz : ∀ j, raw30005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30005step1 = (fun i j => raw30005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30005step1 raw30005step0; decide +kernel
      have hl : raw30005step1Labels = raw30005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30005step0 raw30005step0Labels permutation80 hz
    mixedMoment B raw30005step1 raw30005step1Labels = mixedMoment B raw30005step2 raw30005step2Labels := by
      have ha : raw30005step2 = (fun i j => raw30005step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30005step2 raw30005step1; decide +kernel
      have hl : raw30005step2Labels = raw30005step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30005step1 raw30005step1Labels permutation13 permutation5
    mixedMoment B raw30005step2 raw30005step2Labels = mixedMoment B raw30005step3 raw30005step3Labels := by
      have ha : raw30005step3 = -raw30005step2 := by apply Matrix.ext; change ∀ i j, raw30005step3 i j = -(raw30005step2 i j); unfold raw30005step3 raw30005step2; decide +kernel
      have hl : raw30005step3Labels = raw30005step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30005step3 raw30005step3Labels = mixedMoment B raw30005step4 raw30005step4Labels := by
      have ha : raw30005step4 = raw30005step3 := by apply Matrix.ext; unfold raw30005step4 raw30005step3; decide +kernel
      have hl : raw30005step3Labels = labelEmbedding1 ∘ raw30005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30005step3 raw30005step3Labels raw30005step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw30006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30006 raw30006Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw30006 raw30006Labels = mixedMoment B raw30006step0 raw30006step0Labels := by
      have hz : ∀ j, raw30006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30006step0 = (fun i j => raw30006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30006step0 raw30006; decide +kernel
      have hl : raw30006step0Labels = raw30006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30006 raw30006Labels permutation434 hz
    mixedMoment B raw30006step0 raw30006step0Labels = mixedMoment B raw30006step1 raw30006step1Labels := by
      have ha : raw30006step1 = (fun i j => raw30006step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30006step1 raw30006step0; decide +kernel
      have hl : raw30006step1Labels = raw30006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30006step0 raw30006step0Labels permutation44 permutation5
    mixedMoment B raw30006step1 raw30006step1Labels = mixedMoment B raw30006step2 raw30006step2Labels := by
      have ha : raw30006step2 = -raw30006step1 := by apply Matrix.ext; change ∀ i j, raw30006step2 i j = -(raw30006step1 i j); unfold raw30006step2 raw30006step1; decide +kernel
      have hl : raw30006step2Labels = raw30006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30006step2 raw30006step2Labels = mixedMoment B raw30006step3 raw30006step3Labels := by
      have ha : raw30006step3 = raw30006step2 := by apply Matrix.ext; unfold raw30006step3 raw30006step2; decide +kernel
      have hl : raw30006step2Labels = labelEmbedding1 ∘ raw30006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30006step2 raw30006step2Labels raw30006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw30007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30007step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30007 raw30007Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw30007 raw30007Labels = mixedMoment B raw30007step0 raw30007step0Labels := by
      have hz : ∀ j, raw30007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30007step0 = (fun i j => raw30007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30007step0 raw30007; decide +kernel
      have hl : raw30007step0Labels = raw30007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30007 raw30007Labels permutation434 hz
    mixedMoment B raw30007step0 raw30007step0Labels = mixedMoment B raw30007step1 raw30007step1Labels := by
      have ha : raw30007step1 = (fun i j => raw30007step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30007step1 raw30007step0; decide +kernel
      have hl : raw30007step1Labels = raw30007step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30007step0 raw30007step0Labels permutation34 permutation5
    mixedMoment B raw30007step1 raw30007step1Labels = mixedMoment B raw30007step2 raw30007step2Labels := by
      have ha : raw30007step2 = -raw30007step1 := by apply Matrix.ext; change ∀ i j, raw30007step2 i j = -(raw30007step1 i j); unfold raw30007step2 raw30007step1; decide +kernel
      have hl : raw30007step2Labels = raw30007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30007step2 raw30007step2Labels = mixedMoment B raw30007step3 raw30007step3Labels := by
      have ha : raw30007step3 = raw30007step2 := by apply Matrix.ext; unfold raw30007step3 raw30007step2; decide +kernel
      have hl : raw30007step2Labels = labelEmbedding1 ∘ raw30007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30007step2 raw30007step2Labels raw30007step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw30008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30008 raw30008Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw30008 raw30008Labels = mixedMoment B raw30008step0 raw30008step0Labels := by
      have ha : raw30008step0 = (fun i j => raw30008 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30008step0 raw30008; decide +kernel
      have hl : raw30008step0Labels = raw30008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30008 raw30008Labels permutation212 permutation5
    mixedMoment B raw30008step0 raw30008step0Labels = mixedMoment B raw30008step1 raw30008step1Labels := by
      have ha : raw30008step1 = -raw30008step0 := by apply Matrix.ext; change ∀ i j, raw30008step1 i j = -(raw30008step0 i j); unfold raw30008step1 raw30008step0; decide +kernel
      have hl : raw30008step1Labels = raw30008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30008step1 raw30008step1Labels = mixedMoment B raw30008step2 raw30008step2Labels := by
      have ha : raw30008step2 = raw30008step1 := by apply Matrix.ext; unfold raw30008step2 raw30008step1; decide +kernel
      have hl : raw30008step1Labels = labelEmbedding1 ∘ raw30008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30008step1 raw30008step1Labels raw30008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw30009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30009 raw30009Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw30009 raw30009Labels = mixedMoment B raw30009step0 raw30009step0Labels := by
      have hz : ∀ j, raw30009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30009step0 = (fun i j => raw30009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30009step0 raw30009; decide +kernel
      have hl : raw30009step0Labels = raw30009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30009 raw30009Labels permutation434 hz
    mixedMoment B raw30009step0 raw30009step0Labels = mixedMoment B raw30009step1 raw30009step1Labels := by
      have ha : raw30009step1 = (fun i j => raw30009step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30009step1 raw30009step0; decide +kernel
      have hl : raw30009step1Labels = raw30009step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30009step0 raw30009step0Labels permutation54 permutation5
    mixedMoment B raw30009step1 raw30009step1Labels = mixedMoment B raw30009step2 raw30009step2Labels := by
      have ha : raw30009step2 = -raw30009step1 := by apply Matrix.ext; change ∀ i j, raw30009step2 i j = -(raw30009step1 i j); unfold raw30009step2 raw30009step1; decide +kernel
      have hl : raw30009step2Labels = raw30009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30009step2 raw30009step2Labels = mixedMoment B raw30009step3 raw30009step3Labels := by
      have ha : raw30009step3 = raw30009step2 := by apply Matrix.ext; unfold raw30009step3 raw30009step2; decide +kernel
      have hl : raw30009step2Labels = labelEmbedding1 ∘ raw30009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30009step2 raw30009step2Labels raw30009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw30010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30010 raw30010Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw30010 raw30010Labels = mixedMoment B raw30010step0 raw30010step0Labels := by
      have hz : ∀ j, raw30010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30010step0 = (fun i j => raw30010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30010step0 raw30010; decide +kernel
      have hl : raw30010step0Labels = raw30010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30010 raw30010Labels permutation346 hz
    mixedMoment B raw30010step0 raw30010step0Labels = mixedMoment B raw30010step1 raw30010step1Labels := by
      have ha : raw30010step1 = (fun i j => raw30010step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30010step1 raw30010step0; decide +kernel
      have hl : raw30010step1Labels = raw30010step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30010step0 raw30010step0Labels permutation44 permutation5
    mixedMoment B raw30010step1 raw30010step1Labels = mixedMoment B raw30010step2 raw30010step2Labels := by
      have ha : raw30010step2 = -raw30010step1 := by apply Matrix.ext; change ∀ i j, raw30010step2 i j = -(raw30010step1 i j); unfold raw30010step2 raw30010step1; decide +kernel
      have hl : raw30010step2Labels = raw30010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30010step2 raw30010step2Labels = mixedMoment B raw30010step3 raw30010step3Labels := by
      have ha : raw30010step3 = raw30010step2 := by apply Matrix.ext; unfold raw30010step3 raw30010step2; decide +kernel
      have hl : raw30010step2Labels = labelEmbedding1 ∘ raw30010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30010step2 raw30010step2Labels raw30010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw30011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw30011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw30011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30011 raw30011Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw30011 raw30011Labels = mixedMoment B raw30011step0 raw30011step0Labels := by
      have hz : ∀ j, raw30011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30011step0 = (fun i j => raw30011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30011step0 raw30011; decide +kernel
      have hl : raw30011step0Labels = raw30011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30011 raw30011Labels permutation346 hz
    mixedMoment B raw30011step0 raw30011step0Labels = mixedMoment B raw30011step1 raw30011step1Labels := by
      have ha : raw30011step1 = (fun i j => raw30011step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30011step1 raw30011step0; decide +kernel
      have hl : raw30011step1Labels = raw30011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30011step0 raw30011step0Labels permutation34 permutation5
    mixedMoment B raw30011step1 raw30011step1Labels = mixedMoment B raw30011step2 raw30011step2Labels := by
      have ha : raw30011step2 = -raw30011step1 := by apply Matrix.ext; change ∀ i j, raw30011step2 i j = -(raw30011step1 i j); unfold raw30011step2 raw30011step1; decide +kernel
      have hl : raw30011step2Labels = raw30011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30011step2 raw30011step2Labels = mixedMoment B raw30011step3 raw30011step3Labels := by
      have ha : raw30011step3 = raw30011step2 := by apply Matrix.ext; unfold raw30011step3 raw30011step2; decide +kernel
      have hl : raw30011step2Labels = labelEmbedding1 ∘ raw30011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30011step2 raw30011step2Labels raw30011step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw30012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30012step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw30012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30012 raw30012Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw30012 raw30012Labels = mixedMoment B raw30012step0 raw30012step0Labels := by
      have ha : raw30012step0 = (fun i j => raw30012 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30012step0 raw30012; decide +kernel
      have hl : raw30012step0Labels = raw30012Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30012 raw30012Labels permutation188 permutation5
    mixedMoment B raw30012step0 raw30012step0Labels = mixedMoment B raw30012step1 raw30012step1Labels := by
      have ha : raw30012step1 = -raw30012step0 := by apply Matrix.ext; change ∀ i j, raw30012step1 i j = -(raw30012step0 i j); unfold raw30012step1 raw30012step0; decide +kernel
      have hl : raw30012step1Labels = raw30012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30012step1 raw30012step1Labels = mixedMoment B raw30012step2 raw30012step2Labels := by
      have ha : raw30012step2 = raw30012step1 := by apply Matrix.ext; unfold raw30012step2 raw30012step1; decide +kernel
      have hl : raw30012step1Labels = labelEmbedding1 ∘ raw30012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30012step1 raw30012step1Labels raw30012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw30013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw30013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw30013step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30013 raw30013Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw30013 raw30013Labels = mixedMoment B raw30013step0 raw30013step0Labels := by
      have hz : ∀ j, raw30013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30013step0 = (fun i j => raw30013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30013step0 raw30013; decide +kernel
      have hl : raw30013step0Labels = raw30013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30013 raw30013Labels permutation346 hz
    mixedMoment B raw30013step0 raw30013step0Labels = mixedMoment B raw30013step1 raw30013step1Labels := by
      have ha : raw30013step1 = (fun i j => raw30013step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30013step1 raw30013step0; decide +kernel
      have hl : raw30013step1Labels = raw30013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30013step0 raw30013step0Labels permutation54 permutation5
    mixedMoment B raw30013step1 raw30013step1Labels = mixedMoment B raw30013step2 raw30013step2Labels := by
      have ha : raw30013step2 = -raw30013step1 := by apply Matrix.ext; change ∀ i j, raw30013step2 i j = -(raw30013step1 i j); unfold raw30013step2 raw30013step1; decide +kernel
      have hl : raw30013step2Labels = raw30013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30013step2 raw30013step2Labels = mixedMoment B raw30013step3 raw30013step3Labels := by
      have ha : raw30013step3 = raw30013step2 := by apply Matrix.ext; unfold raw30013step3 raw30013step2; decide +kernel
      have hl : raw30013step2Labels = labelEmbedding1 ∘ raw30013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30013step2 raw30013step2Labels raw30013step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw30014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw30014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30014step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw30014step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30014 raw30014Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw30014 raw30014Labels = mixedMoment B raw30014step0 raw30014step0Labels := by
      have hz : ∀ j, raw30014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30014step0 = (fun i j => raw30014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30014step0 raw30014; decide +kernel
      have hl : raw30014step0Labels = raw30014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30014 raw30014Labels permutation434 hz
    mixedMoment B raw30014step0 raw30014step0Labels = mixedMoment B raw30014step1 raw30014step1Labels := by
      have hz : ∀ j, raw30014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30014step1 = (fun i j => raw30014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30014step1 raw30014step0; decide +kernel
      have hl : raw30014step1Labels = raw30014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30014step0 raw30014step0Labels permutation80 hz
    mixedMoment B raw30014step1 raw30014step1Labels = mixedMoment B raw30014step2 raw30014step2Labels := by
      have ha : raw30014step2 = (fun i j => raw30014step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30014step2 raw30014step1; decide +kernel
      have hl : raw30014step2Labels = raw30014step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30014step1 raw30014step1Labels permutation9 permutation5
    mixedMoment B raw30014step2 raw30014step2Labels = mixedMoment B raw30014step3 raw30014step3Labels := by
      have ha : raw30014step3 = -raw30014step2 := by apply Matrix.ext; change ∀ i j, raw30014step3 i j = -(raw30014step2 i j); unfold raw30014step3 raw30014step2; decide +kernel
      have hl : raw30014step3Labels = raw30014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30014step3 raw30014step3Labels = mixedMoment B raw30014step4 raw30014step4Labels := by
      have ha : raw30014step4 = raw30014step3 := by apply Matrix.ext; unfold raw30014step4 raw30014step3; decide +kernel
      have hl : raw30014step3Labels = labelEmbedding1 ∘ raw30014step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30014step3 raw30014step3Labels raw30014step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw30015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30015step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30015 raw30015Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw30015 raw30015Labels = mixedMoment B raw30015step0 raw30015step0Labels := by
      have hz : ∀ j, raw30015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30015step0 = (fun i j => raw30015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30015step0 raw30015; decide +kernel
      have hl : raw30015step0Labels = raw30015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30015 raw30015Labels permutation434 hz
    mixedMoment B raw30015step0 raw30015step0Labels = mixedMoment B raw30015step1 raw30015step1Labels := by
      have hz : ∀ j, raw30015step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30015step1 = (fun i j => raw30015step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30015step1 raw30015step0; decide +kernel
      have hl : raw30015step1Labels = raw30015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30015step0 raw30015step0Labels permutation80 hz
    mixedMoment B raw30015step1 raw30015step1Labels = mixedMoment B raw30015step2 raw30015step2Labels := by
      have ha : raw30015step2 = (fun i j => raw30015step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30015step2 raw30015step1; decide +kernel
      have hl : raw30015step2Labels = raw30015step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30015step1 raw30015step1Labels permutation24 permutation7
    mixedMoment B raw30015step2 raw30015step2Labels = mixedMoment B raw30015step3 raw30015step3Labels := by
      have ha : raw30015step3 = raw30015step2 := by apply Matrix.ext; unfold raw30015step3 raw30015step2; decide +kernel
      have hl : raw30015step2Labels = labelEmbedding1 ∘ raw30015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30015step2 raw30015step2Labels raw30015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw30016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30016 raw30016Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30016 raw30016Labels = mixedMoment B raw30016step0 raw30016step0Labels := by
      have hz : ∀ j, raw30016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30016step0 = (fun i j => raw30016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30016step0 raw30016; decide +kernel
      have hl : raw30016step0Labels = raw30016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30016 raw30016Labels permutation434 hz
    mixedMoment B raw30016step0 raw30016step0Labels = mixedMoment B raw30016step1 raw30016step1Labels := by
      have ha : raw30016step1 = (fun i j => raw30016step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30016step1 raw30016step0; decide +kernel
      have hl : raw30016step1Labels = raw30016step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30016step0 raw30016step0Labels permutation126 permutation7
    mixedMoment B raw30016step1 raw30016step1Labels = mixedMoment B raw30016step2 raw30016step2Labels := by
      have ha : raw30016step2 = raw30016step1 := by apply Matrix.ext; unfold raw30016step2 raw30016step1; decide +kernel
      have hl : raw30016step1Labels = labelEmbedding1 ∘ raw30016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30016step1 raw30016step1Labels raw30016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw30017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw30017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30017 raw30017Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw30017 raw30017Labels = mixedMoment B raw30017step0 raw30017step0Labels := by
      have hz : ∀ j, raw30017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30017step0 = (fun i j => raw30017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30017step0 raw30017; decide +kernel
      have hl : raw30017step0Labels = raw30017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30017 raw30017Labels permutation346 hz
    mixedMoment B raw30017step0 raw30017step0Labels = mixedMoment B raw30017step1 raw30017step1Labels := by
      have ha : raw30017step1 = (fun i j => raw30017step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30017step1 raw30017step0; decide +kernel
      have hl : raw30017step1Labels = raw30017step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30017step0 raw30017step0Labels permutation126 permutation7
    mixedMoment B raw30017step1 raw30017step1Labels = mixedMoment B raw30017step2 raw30017step2Labels := by
      have ha : raw30017step2 = raw30017step1 := by apply Matrix.ext; unfold raw30017step2 raw30017step1; decide +kernel
      have hl : raw30017step1Labels = labelEmbedding1 ∘ raw30017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30017step1 raw30017step1Labels raw30017step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw30018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![3, -1, -2], ![1, 0, -1]]
def raw30018step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw30018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30018 raw30018Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw30018 raw30018Labels = mixedMoment B raw30018step0 raw30018step0Labels := by
      have hz : ∀ j, raw30018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30018step0 = (fun i j => raw30018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30018step0 raw30018; decide +kernel
      have hl : raw30018step0Labels = raw30018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30018 raw30018Labels permutation434 hz
    mixedMoment B raw30018step0 raw30018step0Labels = mixedMoment B raw30018step1 raw30018step1Labels := by
      have hz : ∀ j, raw30018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30018step1 = (fun i j => raw30018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30018step1 raw30018step0; decide +kernel
      have hl : raw30018step1Labels = raw30018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30018step0 raw30018step0Labels permutation80 hz
    mixedMoment B raw30018step1 raw30018step1Labels = mixedMoment B raw30018step2 raw30018step2Labels := by
      have ha : raw30018step2 = (fun i j => raw30018step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30018step2 raw30018step1; decide +kernel
      have hl : raw30018step2Labels = raw30018step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30018step1 raw30018step1Labels permutation24 permutation7
    mixedMoment B raw30018step2 raw30018step2Labels = mixedMoment B raw30018step3 raw30018step3Labels := by
      have ha : raw30018step3 = raw30018step2 := by apply Matrix.ext; unfold raw30018step3 raw30018step2; decide +kernel
      have hl : raw30018step2Labels = labelEmbedding1 ∘ raw30018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30018step2 raw30018step2Labels raw30018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw30019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30019step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30019step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30019step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30019 raw30019Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw30019 raw30019Labels = mixedMoment B raw30019step0 raw30019step0Labels := by
      have hz : ∀ j, raw30019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30019step0 = (fun i j => raw30019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30019step0 raw30019; decide +kernel
      have hl : raw30019step0Labels = raw30019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30019 raw30019Labels permutation434 hz
    mixedMoment B raw30019step0 raw30019step0Labels = mixedMoment B raw30019step1 raw30019step1Labels := by
      have hz : ∀ j, raw30019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30019step1 = (fun i j => raw30019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30019step1 raw30019step0; decide +kernel
      have hl : raw30019step1Labels = raw30019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30019step0 raw30019step0Labels permutation80 hz
    mixedMoment B raw30019step1 raw30019step1Labels = mixedMoment B raw30019step2 raw30019step2Labels := by
      have ha : raw30019step2 = (fun i j => raw30019step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30019step2 raw30019step1; decide +kernel
      have hl : raw30019step2Labels = raw30019step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30019step1 raw30019step1Labels permutation10 permutation5
    mixedMoment B raw30019step2 raw30019step2Labels = mixedMoment B raw30019step3 raw30019step3Labels := by
      have ha : raw30019step3 = -raw30019step2 := by apply Matrix.ext; change ∀ i j, raw30019step3 i j = -(raw30019step2 i j); unfold raw30019step3 raw30019step2; decide +kernel
      have hl : raw30019step3Labels = raw30019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30019step3 raw30019step3Labels = mixedMoment B raw30019step4 raw30019step4Labels := by
      have ha : raw30019step4 = raw30019step3 := by apply Matrix.ext; unfold raw30019step4 raw30019step3; decide +kernel
      have hl : raw30019step3Labels = labelEmbedding1 ∘ raw30019step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30019step3 raw30019step3Labels raw30019step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw30020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw30020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw30020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30020 raw30020Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw30020 raw30020Labels = mixedMoment B raw30020step0 raw30020step0Labels := by
      have hz : ∀ j, raw30020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30020step0 = (fun i j => raw30020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30020step0 raw30020; decide +kernel
      have hl : raw30020step0Labels = raw30020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30020 raw30020Labels permutation434 hz
    mixedMoment B raw30020step0 raw30020step0Labels = mixedMoment B raw30020step1 raw30020step1Labels := by
      have hz : ∀ j, raw30020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30020step1 = (fun i j => raw30020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30020step1 raw30020step0; decide +kernel
      have hl : raw30020step1Labels = raw30020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30020step0 raw30020step0Labels permutation80 hz
    mixedMoment B raw30020step1 raw30020step1Labels = mixedMoment B raw30020step2 raw30020step2Labels := by
      have ha : raw30020step2 = (fun i j => raw30020step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30020step2 raw30020step1; decide +kernel
      have hl : raw30020step2Labels = raw30020step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30020step1 raw30020step1Labels permutation31 permutation5
    mixedMoment B raw30020step2 raw30020step2Labels = mixedMoment B raw30020step3 raw30020step3Labels := by
      have ha : raw30020step3 = raw30020step2 := by apply Matrix.ext; unfold raw30020step3 raw30020step2; decide +kernel
      have hl : raw30020step2Labels = labelEmbedding1 ∘ raw30020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30020step2 raw30020step2Labels raw30020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3596 node3596Labels := by rfl

def raw30021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30021step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30021 raw30021Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30021 raw30021Labels = mixedMoment B raw30021step0 raw30021step0Labels := by
      have hz : ∀ j, raw30021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30021step0 = (fun i j => raw30021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30021step0 raw30021; decide +kernel
      have hl : raw30021step0Labels = raw30021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30021 raw30021Labels permutation434 hz
    mixedMoment B raw30021step0 raw30021step0Labels = mixedMoment B raw30021step1 raw30021step1Labels := by
      have ha : raw30021step1 = (fun i j => raw30021step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30021step1 raw30021step0; decide +kernel
      have hl : raw30021step1Labels = raw30021step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30021step0 raw30021step0Labels permutation40 permutation5
    mixedMoment B raw30021step1 raw30021step1Labels = mixedMoment B raw30021step2 raw30021step2Labels := by
      have ha : raw30021step2 = -raw30021step1 := by apply Matrix.ext; change ∀ i j, raw30021step2 i j = -(raw30021step1 i j); unfold raw30021step2 raw30021step1; decide +kernel
      have hl : raw30021step2Labels = raw30021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30021step2 raw30021step2Labels = mixedMoment B raw30021step3 raw30021step3Labels := by
      have ha : raw30021step3 = raw30021step2 := by apply Matrix.ext; unfold raw30021step3 raw30021step2; decide +kernel
      have hl : raw30021step2Labels = labelEmbedding1 ∘ raw30021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30021step2 raw30021step2Labels raw30021step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw30022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30022 raw30022Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw30022 raw30022Labels = mixedMoment B raw30022step0 raw30022step0Labels := by
      have hz : ∀ j, raw30022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30022step0 = (fun i j => raw30022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30022step0 raw30022; decide +kernel
      have hl : raw30022step0Labels = raw30022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30022 raw30022Labels permutation346 hz
    mixedMoment B raw30022step0 raw30022step0Labels = mixedMoment B raw30022step1 raw30022step1Labels := by
      have ha : raw30022step1 = (fun i j => raw30022step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30022step1 raw30022step0; decide +kernel
      have hl : raw30022step1Labels = raw30022step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30022step0 raw30022step0Labels permutation40 permutation5
    mixedMoment B raw30022step1 raw30022step1Labels = mixedMoment B raw30022step2 raw30022step2Labels := by
      have ha : raw30022step2 = -raw30022step1 := by apply Matrix.ext; change ∀ i j, raw30022step2 i j = -(raw30022step1 i j); unfold raw30022step2 raw30022step1; decide +kernel
      have hl : raw30022step2Labels = raw30022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30022step2 raw30022step2Labels = mixedMoment B raw30022step3 raw30022step3Labels := by
      have ha : raw30022step3 = raw30022step2 := by apply Matrix.ext; unfold raw30022step3 raw30022step2; decide +kernel
      have hl : raw30022step2Labels = labelEmbedding1 ∘ raw30022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30022step2 raw30022step2Labels raw30022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw30023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30023 raw30023Labels = mixedMoment B node3707 node3707Labels := by
  calc
    mixedMoment B raw30023 raw30023Labels = mixedMoment B raw30023step0 raw30023step0Labels := by
      have hz : ∀ j, raw30023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30023step0 = (fun i j => raw30023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30023step0 raw30023; decide +kernel
      have hl : raw30023step0Labels = raw30023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30023 raw30023Labels permutation434 hz
    mixedMoment B raw30023step0 raw30023step0Labels = mixedMoment B raw30023step1 raw30023step1Labels := by
      have hz : ∀ j, raw30023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30023step1 = (fun i j => raw30023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30023step1 raw30023step0; decide +kernel
      have hl : raw30023step1Labels = raw30023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30023step0 raw30023step0Labels permutation80 hz
    mixedMoment B raw30023step1 raw30023step1Labels = mixedMoment B raw30023step2 raw30023step2Labels := by
      have ha : raw30023step2 = (fun i j => raw30023step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30023step2 raw30023step1; decide +kernel
      have hl : raw30023step2Labels = raw30023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30023step1 raw30023step1Labels permutation15 permutation2
    _ = mixedMoment B node3707 node3707Labels := by rfl

def raw30024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw30024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30024 raw30024Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw30024 raw30024Labels = mixedMoment B raw30024step0 raw30024step0Labels := by
      have hz : ∀ j, raw30024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30024step0 = (fun i j => raw30024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30024step0 raw30024; decide +kernel
      have hl : raw30024step0Labels = raw30024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30024 raw30024Labels permutation434 hz
    mixedMoment B raw30024step0 raw30024step0Labels = mixedMoment B raw30024step1 raw30024step1Labels := by
      have hz : ∀ j, raw30024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30024step1 = (fun i j => raw30024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30024step1 raw30024step0; decide +kernel
      have hl : raw30024step1Labels = raw30024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30024step0 raw30024step0Labels permutation80 hz
    mixedMoment B raw30024step1 raw30024step1Labels = mixedMoment B raw30024step2 raw30024step2Labels := by
      have ha : raw30024step2 = (fun i j => raw30024step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30024step2 raw30024step1; decide +kernel
      have hl : raw30024step2Labels = raw30024step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30024step1 raw30024step1Labels permutation9 permutation2
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw30025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30025 raw30025Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw30025 raw30025Labels = mixedMoment B raw30025step0 raw30025step0Labels := by
      have hz : ∀ j, raw30025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30025step0 = (fun i j => raw30025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30025step0 raw30025; decide +kernel
      have hl : raw30025step0Labels = raw30025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30025 raw30025Labels permutation434 hz
    mixedMoment B raw30025step0 raw30025step0Labels = mixedMoment B raw30025step1 raw30025step1Labels := by
      have ha : raw30025step1 = (fun i j => raw30025step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30025step1 raw30025step0; decide +kernel
      have hl : raw30025step1Labels = raw30025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30025step0 raw30025step0Labels permutation33 permutation2
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw30026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30026 raw30026Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw30026 raw30026Labels = mixedMoment B raw30026step0 raw30026step0Labels := by
      have hz : ∀ j, raw30026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30026step0 = (fun i j => raw30026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30026step0 raw30026; decide +kernel
      have hl : raw30026step0Labels = raw30026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30026 raw30026Labels permutation346 hz
    mixedMoment B raw30026step0 raw30026step0Labels = mixedMoment B raw30026step1 raw30026step1Labels := by
      have ha : raw30026step1 = (fun i j => raw30026step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30026step1 raw30026step0; decide +kernel
      have hl : raw30026step1Labels = raw30026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30026step0 raw30026step0Labels permutation33 permutation2
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw30027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![3, -1, -2], ![2, -1, -1]]
def raw30027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30027 raw30027Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw30027 raw30027Labels = mixedMoment B raw30027step0 raw30027step0Labels := by
      have hz : ∀ j, raw30027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30027step0 = (fun i j => raw30027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30027step0 raw30027; decide +kernel
      have hl : raw30027step0Labels = raw30027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30027 raw30027Labels permutation434 hz
    mixedMoment B raw30027step0 raw30027step0Labels = mixedMoment B raw30027step1 raw30027step1Labels := by
      have hz : ∀ j, raw30027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30027step1 = (fun i j => raw30027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30027step1 raw30027step0; decide +kernel
      have hl : raw30027step1Labels = raw30027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30027step0 raw30027step0Labels permutation80 hz
    mixedMoment B raw30027step1 raw30027step1Labels = mixedMoment B raw30027step2 raw30027step2Labels := by
      have ha : raw30027step2 = (fun i j => raw30027step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30027step2 raw30027step1; decide +kernel
      have hl : raw30027step2Labels = raw30027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30027step1 raw30027step1Labels permutation25 permutation2
    mixedMoment B raw30027step2 raw30027step2Labels = mixedMoment B raw30027step3 raw30027step3Labels := by
      have ha : raw30027step3 = -raw30027step2 := by apply Matrix.ext; change ∀ i j, raw30027step3 i j = -(raw30027step2 i j); unfold raw30027step3 raw30027step2; decide +kernel
      have hl : raw30027step3Labels = raw30027step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw30028 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30028step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30028 raw30028Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30028 raw30028Labels = mixedMoment B raw30028step0 raw30028step0Labels := by
      have hz : ∀ j, raw30028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30028step0 = (fun i j => raw30028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30028step0 raw30028; decide +kernel
      have hl : raw30028step0Labels = raw30028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30028 raw30028Labels permutation434 hz
    mixedMoment B raw30028step0 raw30028step0Labels = mixedMoment B raw30028step1 raw30028step1Labels := by
      have ha : raw30028step1 = (fun i j => raw30028step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30028step1 raw30028step0; decide +kernel
      have hl : raw30028step1Labels = raw30028step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30028step0 raw30028step0Labels permutation33 permutation7
    mixedMoment B raw30028step1 raw30028step1Labels = mixedMoment B raw30028step2 raw30028step2Labels := by
      have ha : raw30028step2 = raw30028step1 := by apply Matrix.ext; unfold raw30028step2 raw30028step1; decide +kernel
      have hl : raw30028step1Labels = labelEmbedding10 ∘ raw30028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30028step1 raw30028step1Labels raw30028step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30029 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30029step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30029 raw30029Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30029 raw30029Labels = mixedMoment B raw30029step0 raw30029step0Labels := by
      have hz : ∀ j, raw30029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30029step0 = (fun i j => raw30029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30029step0 raw30029; decide +kernel
      have hl : raw30029step0Labels = raw30029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30029 raw30029Labels permutation346 hz
    mixedMoment B raw30029step0 raw30029step0Labels = mixedMoment B raw30029step1 raw30029step1Labels := by
      have ha : raw30029step1 = (fun i j => raw30029step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30029step1 raw30029step0; decide +kernel
      have hl : raw30029step1Labels = raw30029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30029step0 raw30029step0Labels permutation33 permutation7
    mixedMoment B raw30029step1 raw30029step1Labels = mixedMoment B raw30029step2 raw30029step2Labels := by
      have ha : raw30029step2 = raw30029step1 := by apply Matrix.ext; unfold raw30029step2 raw30029step1; decide +kernel
      have hl : raw30029step1Labels = labelEmbedding10 ∘ raw30029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30029step1 raw30029step1Labels raw30029step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30030 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-3, 1, 2], ![-1, -1, 2]]
def raw30030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30030 raw30030Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw30030 raw30030Labels = mixedMoment B raw30030step0 raw30030step0Labels := by
      have hz : ∀ j, raw30030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30030step0 = (fun i j => raw30030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30030step0 raw30030; decide +kernel
      have hl : raw30030step0Labels = raw30030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30030 raw30030Labels permutation434 hz
    mixedMoment B raw30030step0 raw30030step0Labels = mixedMoment B raw30030step1 raw30030step1Labels := by
      have hz : ∀ j, raw30030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30030step1 = (fun i j => raw30030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30030step1 raw30030step0; decide +kernel
      have hl : raw30030step1Labels = raw30030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30030step0 raw30030step0Labels permutation80 hz
    mixedMoment B raw30030step1 raw30030step1Labels = mixedMoment B raw30030step2 raw30030step2Labels := by
      have ha : raw30030step2 = (fun i j => raw30030step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30030step2 raw30030step1; decide +kernel
      have hl : raw30030step2Labels = raw30030step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30030step1 raw30030step1Labels permutation25 permutation2
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw30031 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30031step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30031 raw30031Labels = mixedMoment B node5024 node5024Labels := by
  calc
    mixedMoment B raw30031 raw30031Labels = mixedMoment B raw30031step0 raw30031step0Labels := by
      have hz : ∀ j, raw30031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30031step0 = (fun i j => raw30031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30031step0 raw30031; decide +kernel
      have hl : raw30031step0Labels = raw30031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30031 raw30031Labels permutation434 hz
    mixedMoment B raw30031step0 raw30031step0Labels = mixedMoment B raw30031step1 raw30031step1Labels := by
      have hz : ∀ j, raw30031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30031step1 = (fun i j => raw30031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30031step1 raw30031step0; decide +kernel
      have hl : raw30031step1Labels = raw30031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30031step0 raw30031step0Labels permutation80 hz
    mixedMoment B raw30031step1 raw30031step1Labels = mixedMoment B raw30031step2 raw30031step2Labels := by
      have ha : raw30031step2 = (fun i j => raw30031step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30031step2 raw30031step1; decide +kernel
      have hl : raw30031step2Labels = raw30031step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30031step1 raw30031step1Labels permutation8 permutation7
    mixedMoment B raw30031step2 raw30031step2Labels = mixedMoment B raw30031step3 raw30031step3Labels := by
      have ha : raw30031step3 = raw30031step2 := by apply Matrix.ext; unfold raw30031step3 raw30031step2; decide +kernel
      have hl : raw30031step2Labels = labelEmbedding10 ∘ raw30031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30031step2 raw30031step2Labels raw30031step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5024 node5024Labels := by rfl

def raw30032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw30032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30032step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30032 raw30032Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw30032 raw30032Labels = mixedMoment B raw30032step0 raw30032step0Labels := by
      have hz : ∀ j, raw30032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30032step0 = (fun i j => raw30032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30032step0 raw30032; decide +kernel
      have hl : raw30032step0Labels = raw30032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30032 raw30032Labels permutation434 hz
    mixedMoment B raw30032step0 raw30032step0Labels = mixedMoment B raw30032step1 raw30032step1Labels := by
      have hz : ∀ j, raw30032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30032step1 = (fun i j => raw30032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30032step1 raw30032step0; decide +kernel
      have hl : raw30032step1Labels = raw30032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30032step0 raw30032step0Labels permutation80 hz
    mixedMoment B raw30032step1 raw30032step1Labels = mixedMoment B raw30032step2 raw30032step2Labels := by
      have ha : raw30032step2 = (fun i j => raw30032step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30032step2 raw30032step1; decide +kernel
      have hl : raw30032step2Labels = raw30032step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30032step1 raw30032step1Labels permutation8 permutation6
    mixedMoment B raw30032step2 raw30032step2Labels = mixedMoment B raw30032step3 raw30032step3Labels := by
      have ha : raw30032step3 = raw30032step2 := by apply Matrix.ext; unfold raw30032step3 raw30032step2; decide +kernel
      have hl : raw30032step2Labels = labelEmbedding9 ∘ raw30032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30032step2 raw30032step2Labels raw30032step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw30033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw30033step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw30033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30033 raw30033Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw30033 raw30033Labels = mixedMoment B raw30033step0 raw30033step0Labels := by
      have hz : ∀ j, raw30033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30033step0 = (fun i j => raw30033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30033step0 raw30033; decide +kernel
      have hl : raw30033step0Labels = raw30033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30033 raw30033Labels permutation434 hz
    mixedMoment B raw30033step0 raw30033step0Labels = mixedMoment B raw30033step1 raw30033step1Labels := by
      have ha : raw30033step1 = (fun i j => raw30033step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30033step1 raw30033step0; decide +kernel
      have hl : raw30033step1Labels = raw30033step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30033step0 raw30033step0Labels permutation32 permutation6
    mixedMoment B raw30033step1 raw30033step1Labels = mixedMoment B raw30033step2 raw30033step2Labels := by
      have ha : raw30033step2 = raw30033step1 := by apply Matrix.ext; unfold raw30033step2 raw30033step1; decide +kernel
      have hl : raw30033step1Labels = labelEmbedding9 ∘ raw30033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30033step1 raw30033step1Labels raw30033step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw30034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw30034step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw30034step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30034 raw30034Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw30034 raw30034Labels = mixedMoment B raw30034step0 raw30034step0Labels := by
      have hz : ∀ j, raw30034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30034step0 = (fun i j => raw30034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30034step0 raw30034; decide +kernel
      have hl : raw30034step0Labels = raw30034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30034 raw30034Labels permutation346 hz
    mixedMoment B raw30034step0 raw30034step0Labels = mixedMoment B raw30034step1 raw30034step1Labels := by
      have ha : raw30034step1 = (fun i j => raw30034step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30034step1 raw30034step0; decide +kernel
      have hl : raw30034step1Labels = raw30034step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30034step0 raw30034step0Labels permutation32 permutation6
    mixedMoment B raw30034step1 raw30034step1Labels = mixedMoment B raw30034step2 raw30034step2Labels := by
      have ha : raw30034step2 = raw30034step1 := by apply Matrix.ext; unfold raw30034step2 raw30034step1; decide +kernel
      have hl : raw30034step1Labels = labelEmbedding9 ∘ raw30034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30034step1 raw30034step1Labels raw30034step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw30035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-3, 1, 2], ![-1, -1, 2]]
def raw30035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw30035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30035 raw30035Labels = mixedMoment B node5022 node5022Labels := by
  calc
    mixedMoment B raw30035 raw30035Labels = mixedMoment B raw30035step0 raw30035step0Labels := by
      have hz : ∀ j, raw30035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30035step0 = (fun i j => raw30035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30035step0 raw30035; decide +kernel
      have hl : raw30035step0Labels = raw30035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30035 raw30035Labels permutation434 hz
    mixedMoment B raw30035step0 raw30035step0Labels = mixedMoment B raw30035step1 raw30035step1Labels := by
      have hz : ∀ j, raw30035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30035step1 = (fun i j => raw30035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30035step1 raw30035step0; decide +kernel
      have hl : raw30035step1Labels = raw30035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30035step0 raw30035step0Labels permutation80 hz
    mixedMoment B raw30035step1 raw30035step1Labels = mixedMoment B raw30035step2 raw30035step2Labels := by
      have ha : raw30035step2 = (fun i j => raw30035step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30035step2 raw30035step1; decide +kernel
      have hl : raw30035step2Labels = raw30035step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30035step1 raw30035step1Labels permutation24 permutation2
    _ = mixedMoment B node5022 node5022Labels := by rfl

def raw30036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw30036step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30036step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30036step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30036step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30036 raw30036Labels = mixedMoment B node5214 node5214Labels := by
  calc
    mixedMoment B raw30036 raw30036Labels = mixedMoment B raw30036step0 raw30036step0Labels := by
      have hz : ∀ j, raw30036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30036step0 = (fun i j => raw30036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30036step0 raw30036; decide +kernel
      have hl : raw30036step0Labels = raw30036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30036 raw30036Labels permutation434 hz
    mixedMoment B raw30036step0 raw30036step0Labels = mixedMoment B raw30036step1 raw30036step1Labels := by
      have hz : ∀ j, raw30036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30036step1 = (fun i j => raw30036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30036step1 raw30036step0; decide +kernel
      have hl : raw30036step1Labels = raw30036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30036step0 raw30036step0Labels permutation80 hz
    mixedMoment B raw30036step1 raw30036step1Labels = mixedMoment B raw30036step2 raw30036step2Labels := by
      have ha : raw30036step2 = (fun i j => raw30036step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30036step2 raw30036step1; decide +kernel
      have hl : raw30036step2Labels = raw30036step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30036step1 raw30036step1Labels permutation14 permutation3
    mixedMoment B raw30036step2 raw30036step2Labels = mixedMoment B raw30036step3 raw30036step3Labels := by
      have ha : raw30036step3 = -raw30036step2 := by apply Matrix.ext; change ∀ i j, raw30036step3 i j = -(raw30036step2 i j); unfold raw30036step3 raw30036step2; decide +kernel
      have hl : raw30036step3Labels = raw30036step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30036step3 raw30036step3Labels = mixedMoment B raw30036step4 raw30036step4Labels := by
      have ha : raw30036step4 = raw30036step3 := by apply Matrix.ext; unfold raw30036step4 raw30036step3; decide +kernel
      have hl : raw30036step3Labels = labelEmbedding6 ∘ raw30036step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30036step3 raw30036step3Labels raw30036step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5214 node5214Labels := by rfl

def raw30037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30037 raw30037Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw30037 raw30037Labels = mixedMoment B raw30037step0 raw30037step0Labels := by
      have hz : ∀ j, raw30037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30037step0 = (fun i j => raw30037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30037step0 raw30037; decide +kernel
      have hl : raw30037step0Labels = raw30037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30037 raw30037Labels permutation434 hz
    mixedMoment B raw30037step0 raw30037step0Labels = mixedMoment B raw30037step1 raw30037step1Labels := by
      have ha : raw30037step1 = (fun i j => raw30037step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30037step1 raw30037step0; decide +kernel
      have hl : raw30037step1Labels = raw30037step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30037step0 raw30037step0Labels permutation32 permutation6
    mixedMoment B raw30037step1 raw30037step1Labels = mixedMoment B raw30037step2 raw30037step2Labels := by
      have ha : raw30037step2 = raw30037step1 := by apply Matrix.ext; unfold raw30037step2 raw30037step1; decide +kernel
      have hl : raw30037step1Labels = labelEmbedding9 ∘ raw30037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30037step1 raw30037step1Labels raw30037step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw30038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw30038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30038step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30038 raw30038Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw30038 raw30038Labels = mixedMoment B raw30038step0 raw30038step0Labels := by
      have ha : raw30038step0 = (fun i j => raw30038 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30038step0 raw30038; decide +kernel
      have hl : raw30038step0Labels = raw30038Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30038 raw30038Labels permutation158 permutation6
    mixedMoment B raw30038step0 raw30038step0Labels = mixedMoment B raw30038step1 raw30038step1Labels := by
      have ha : raw30038step1 = raw30038step0 := by apply Matrix.ext; unfold raw30038step1 raw30038step0; decide +kernel
      have hl : raw30038step0Labels = labelEmbedding9 ∘ raw30038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30038step0 raw30038step0Labels raw30038step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw30039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw30039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw30039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30039 raw30039Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw30039 raw30039Labels = mixedMoment B raw30039step0 raw30039step0Labels := by
      have hz : ∀ j, raw30039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30039step0 = (fun i j => raw30039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30039step0 raw30039; decide +kernel
      have hl : raw30039step0Labels = raw30039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30039 raw30039Labels permutation434 hz
    mixedMoment B raw30039step0 raw30039step0Labels = mixedMoment B raw30039step1 raw30039step1Labels := by
      have ha : raw30039step1 = (fun i j => raw30039step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30039step1 raw30039step0; decide +kernel
      have hl : raw30039step1Labels = raw30039step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30039step0 raw30039step0Labels permutation126 permutation2
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw30040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30040step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30040 raw30040Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw30040 raw30040Labels = mixedMoment B raw30040step0 raw30040step0Labels := by
      have hz : ∀ j, raw30040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30040step0 = (fun i j => raw30040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30040step0 raw30040; decide +kernel
      have hl : raw30040step0Labels = raw30040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30040 raw30040Labels permutation434 hz
    mixedMoment B raw30040step0 raw30040step0Labels = mixedMoment B raw30040step1 raw30040step1Labels := by
      have ha : raw30040step1 = (fun i j => raw30040step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30040step1 raw30040step0; decide +kernel
      have hl : raw30040step1Labels = raw30040step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30040step0 raw30040step0Labels permutation32 permutation6
    mixedMoment B raw30040step1 raw30040step1Labels = mixedMoment B raw30040step2 raw30040step2Labels := by
      have ha : raw30040step2 = raw30040step1 := by apply Matrix.ext; unfold raw30040step2 raw30040step1; decide +kernel
      have hl : raw30040step1Labels = labelEmbedding9 ∘ raw30040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30040step1 raw30040step1Labels raw30040step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw30041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30041 raw30041Labels = mixedMoment B node3654 node3654Labels := by
  calc
    mixedMoment B raw30041 raw30041Labels = mixedMoment B raw30041step0 raw30041step0Labels := by
      have hz : ∀ j, raw30041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30041step0 = (fun i j => raw30041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30041step0 raw30041; decide +kernel
      have hl : raw30041step0Labels = raw30041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30041 raw30041Labels permutation346 hz
    mixedMoment B raw30041step0 raw30041step0Labels = mixedMoment B raw30041step1 raw30041step1Labels := by
      have ha : raw30041step1 = (fun i j => raw30041step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30041step1 raw30041step0; decide +kernel
      have hl : raw30041step1Labels = raw30041step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30041step0 raw30041step0Labels permutation126 permutation2
    mixedMoment B raw30041step1 raw30041step1Labels = mixedMoment B raw30041step2 raw30041step2Labels := by
      have ha : raw30041step2 = -raw30041step1 := by apply Matrix.ext; change ∀ i j, raw30041step2 i j = -(raw30041step1 i j); unfold raw30041step2 raw30041step1; decide +kernel
      have hl : raw30041step2Labels = raw30041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3654 node3654Labels := by rfl

def raw30042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30042 raw30042Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw30042 raw30042Labels = mixedMoment B raw30042step0 raw30042step0Labels := by
      have hz : ∀ j, raw30042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30042step0 = (fun i j => raw30042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30042step0 raw30042; decide +kernel
      have hl : raw30042step0Labels = raw30042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30042 raw30042Labels permutation346 hz
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw30043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30043 raw30043Labels = mixedMoment B node2795 node2795Labels := by
  calc
    mixedMoment B raw30043 raw30043Labels = mixedMoment B raw30043step0 raw30043step0Labels := by
      have ha : raw30043step0 = (fun i j => raw30043 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30043step0 raw30043; decide +kernel
      have hl : raw30043step0Labels = raw30043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30043 raw30043Labels permutation158 permutation2
    _ = mixedMoment B node2795 node2795Labels := by rfl

def raw30044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30044 raw30044Labels = mixedMoment B node2805 node2805Labels := by
  calc
    mixedMoment B raw30044 raw30044Labels = mixedMoment B raw30044step0 raw30044step0Labels := by
      have hz : ∀ j, raw30044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30044step0 = (fun i j => raw30044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30044step0 raw30044; decide +kernel
      have hl : raw30044step0Labels = raw30044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30044 raw30044Labels permutation346 hz
    _ = mixedMoment B node2805 node2805Labels := by rfl

def raw30045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30045 raw30045Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw30045 raw30045Labels = mixedMoment B raw30045step0 raw30045step0Labels := by
      have hz : ∀ j, raw30045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30045step0 = (fun i j => raw30045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30045step0 raw30045; decide +kernel
      have hl : raw30045step0Labels = raw30045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30045 raw30045Labels permutation346 hz
    mixedMoment B raw30045step0 raw30045step0Labels = mixedMoment B raw30045step1 raw30045step1Labels := by
      have ha : raw30045step1 = (fun i j => raw30045step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30045step1 raw30045step0; decide +kernel
      have hl : raw30045step1Labels = raw30045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30045step0 raw30045step0Labels permutation127 permutation2
    mixedMoment B raw30045step1 raw30045step1Labels = mixedMoment B raw30045step2 raw30045step2Labels := by
      have ha : raw30045step2 = -raw30045step1 := by apply Matrix.ext; change ∀ i j, raw30045step2 i j = -(raw30045step1 i j); unfold raw30045step2 raw30045step1; decide +kernel
      have hl : raw30045step2Labels = raw30045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw30046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30046 raw30046Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw30046 raw30046Labels = mixedMoment B raw30046step0 raw30046step0Labels := by
      have hz : ∀ j, raw30046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30046step0 = (fun i j => raw30046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30046step0 raw30046; decide +kernel
      have hl : raw30046step0Labels = raw30046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30046 raw30046Labels permutation346 hz
    mixedMoment B raw30046step0 raw30046step0Labels = mixedMoment B raw30046step1 raw30046step1Labels := by
      have ha : raw30046step1 = (fun i j => raw30046step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30046step1 raw30046step0; decide +kernel
      have hl : raw30046step1Labels = raw30046step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30046step0 raw30046step0Labels permutation151 permutation2
    mixedMoment B raw30046step1 raw30046step1Labels = mixedMoment B raw30046step2 raw30046step2Labels := by
      have ha : raw30046step2 = -raw30046step1 := by apply Matrix.ext; change ∀ i j, raw30046step2 i j = -(raw30046step1 i j); unfold raw30046step2 raw30046step1; decide +kernel
      have hl : raw30046step2Labels = raw30046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw30047 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw30047Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw30047step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30047step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30047step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30047step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30047step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30047 raw30047Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30047 raw30047Labels = mixedMoment B raw30047step0 raw30047step0Labels := by
      have hz : ∀ j, raw30047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30047step0 = (fun i j => raw30047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30047step0 raw30047; decide +kernel
      have hl : raw30047step0Labels = raw30047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30047 raw30047Labels permutation346 hz
    mixedMoment B raw30047step0 raw30047step0Labels = mixedMoment B raw30047step1 raw30047step1Labels := by
      have ha : raw30047step1 = (fun i j => raw30047step0 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30047step1 raw30047step0; decide +kernel
      have hl : raw30047step1Labels = raw30047step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30047step0 raw30047step0Labels permutation123 permutation0
    mixedMoment B raw30047step1 raw30047step1Labels = mixedMoment B raw30047step2 raw30047step2Labels := by
      have ha : raw30047step2 = -raw30047step1 := by apply Matrix.ext; change ∀ i j, raw30047step2 i j = -(raw30047step1 i j); unfold raw30047step2 raw30047step1; decide +kernel
      have hl : raw30047step2Labels = raw30047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30048 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30048 raw30048Labels = mixedMoment B node3332 node3332Labels := by
  calc
    mixedMoment B raw30048 raw30048Labels = mixedMoment B raw30048step0 raw30048step0Labels := by
      have ha : raw30048step0 = (fun i j => raw30048 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30048step0 raw30048; decide +kernel
      have hl : raw30048step0Labels = raw30048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30048 raw30048Labels permutation158 permutation2
    mixedMoment B raw30048step0 raw30048step0Labels = mixedMoment B raw30048step1 raw30048step1Labels := by
      have ha : raw30048step1 = -raw30048step0 := by apply Matrix.ext; change ∀ i j, raw30048step1 i j = -(raw30048step0 i j); unfold raw30048step1 raw30048step0; decide +kernel
      have hl : raw30048step1Labels = raw30048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3332 node3332Labels := by rfl

def raw30049 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30049 raw30049Labels = mixedMoment B node3361 node3361Labels := by
  calc
    mixedMoment B raw30049 raw30049Labels = mixedMoment B raw30049step0 raw30049step0Labels := by
      have hz : ∀ j, raw30049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30049step0 = (fun i j => raw30049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30049step0 raw30049; decide +kernel
      have hl : raw30049step0Labels = raw30049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30049 raw30049Labels permutation434 hz
    mixedMoment B raw30049step0 raw30049step0Labels = mixedMoment B raw30049step1 raw30049step1Labels := by
      have hz : ∀ j, raw30049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30049step1 = (fun i j => raw30049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30049step1 raw30049step0; decide +kernel
      have hl : raw30049step1Labels = raw30049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30049step0 raw30049step0Labels permutation80 hz
    mixedMoment B raw30049step1 raw30049step1Labels = mixedMoment B raw30049step2 raw30049step2Labels := by
      have ha : raw30049step2 = -raw30049step1 := by apply Matrix.ext; change ∀ i j, raw30049step2 i j = -(raw30049step1 i j); unfold raw30049step2 raw30049step1; decide +kernel
      have hl : raw30049step2Labels = raw30049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3361 node3361Labels := by rfl

def raw30050 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw30050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-2, 0, 2]]
def raw30050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30050 raw30050Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw30050 raw30050Labels = mixedMoment B raw30050step0 raw30050step0Labels := by
      have hz : ∀ j, raw30050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30050step0 = (fun i j => raw30050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30050step0 raw30050; decide +kernel
      have hl : raw30050step0Labels = raw30050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30050 raw30050Labels permutation346 hz
    mixedMoment B raw30050step0 raw30050step0Labels = mixedMoment B raw30050step1 raw30050step1Labels := by
      have ha : raw30050step1 = (fun i j => raw30050step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30050step1 raw30050step0; decide +kernel
      have hl : raw30050step1Labels = raw30050step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30050step0 raw30050step0Labels permutation127 permutation2
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw30051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw30051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw30051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30051 raw30051Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw30051 raw30051Labels = mixedMoment B raw30051step0 raw30051step0Labels := by
      have hz : ∀ j, raw30051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30051step0 = (fun i j => raw30051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30051step0 raw30051; decide +kernel
      have hl : raw30051step0Labels = raw30051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30051 raw30051Labels permutation346 hz
    mixedMoment B raw30051step0 raw30051step0Labels = mixedMoment B raw30051step1 raw30051step1Labels := by
      have ha : raw30051step1 = (fun i j => raw30051step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30051step1 raw30051step0; decide +kernel
      have hl : raw30051step1Labels = raw30051step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30051step0 raw30051step0Labels permutation151 permutation2
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw30052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, -1, 3], ![2, 0, -2], ![2, 0, -2]]
def raw30052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30052 raw30052Labels = mixedMoment B node3361 node3361Labels := by
  calc
    mixedMoment B raw30052 raw30052Labels = mixedMoment B raw30052step0 raw30052step0Labels := by
      have hz : ∀ j, raw30052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30052step0 = (fun i j => raw30052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30052step0 raw30052; decide +kernel
      have hl : raw30052step0Labels = raw30052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30052 raw30052Labels permutation434 hz
    mixedMoment B raw30052step0 raw30052step0Labels = mixedMoment B raw30052step1 raw30052step1Labels := by
      have hz : ∀ j, raw30052step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30052step1 = (fun i j => raw30052step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30052step1 raw30052step0; decide +kernel
      have hl : raw30052step1Labels = raw30052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30052step0 raw30052step0Labels permutation80 hz
    mixedMoment B raw30052step1 raw30052step1Labels = mixedMoment B raw30052step2 raw30052step2Labels := by
      have ha : raw30052step2 = (fun i j => raw30052step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30052step2 raw30052step1; decide +kernel
      have hl : raw30052step2Labels = raw30052step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30052step1 raw30052step1Labels permutation14 permutation2
    _ = mixedMoment B node3361 node3361Labels := by rfl

def raw30053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw30053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30053 raw30053Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw30053 raw30053Labels = mixedMoment B raw30053step0 raw30053step0Labels := by
      have hz : ∀ j, raw30053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30053step0 = (fun i j => raw30053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30053step0 raw30053; decide +kernel
      have hl : raw30053step0Labels = raw30053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30053 raw30053Labels permutation434 hz
    mixedMoment B raw30053step0 raw30053step0Labels = mixedMoment B raw30053step1 raw30053step1Labels := by
      have hz : ∀ j, raw30053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30053step1 = (fun i j => raw30053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30053step1 raw30053step0; decide +kernel
      have hl : raw30053step1Labels = raw30053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30053step0 raw30053step0Labels permutation80 hz
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw30054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30054 raw30054Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw30054 raw30054Labels = mixedMoment B raw30054step0 raw30054step0Labels := by
      have hz : ∀ j, raw30054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30054step0 = (fun i j => raw30054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30054step0 raw30054; decide +kernel
      have hl : raw30054step0Labels = raw30054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30054 raw30054Labels permutation434 hz
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw30055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30055 raw30055Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw30055 raw30055Labels = mixedMoment B raw30055step0 raw30055step0Labels := by
      have hz : ∀ j, raw30055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30055step0 = (fun i j => raw30055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30055step0 raw30055; decide +kernel
      have hl : raw30055step0Labels = raw30055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30055 raw30055Labels permutation346 hz
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw30056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, 0, -2]]
def raw30056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![3, -1, -2], ![2, 0, -2]]
def raw30056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-2, -1, 3], ![-3, 2, 1]]
def raw30056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30056 raw30056Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw30056 raw30056Labels = mixedMoment B raw30056step0 raw30056step0Labels := by
      have hz : ∀ j, raw30056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30056step0 = (fun i j => raw30056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30056step0 raw30056; decide +kernel
      have hl : raw30056step0Labels = raw30056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30056 raw30056Labels permutation434 hz
    mixedMoment B raw30056step0 raw30056step0Labels = mixedMoment B raw30056step1 raw30056step1Labels := by
      have hz : ∀ j, raw30056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30056step1 = (fun i j => raw30056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30056step1 raw30056step0; decide +kernel
      have hl : raw30056step1Labels = raw30056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30056step0 raw30056step0Labels permutation80 hz
    mixedMoment B raw30056step1 raw30056step1Labels = mixedMoment B raw30056step2 raw30056step2Labels := by
      have ha : raw30056step2 = (fun i j => raw30056step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30056step2 raw30056step1; decide +kernel
      have hl : raw30056step2Labels = raw30056step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30056step1 raw30056step1Labels permutation25 permutation2
    mixedMoment B raw30056step2 raw30056step2Labels = mixedMoment B raw30056step3 raw30056step3Labels := by
      have ha : raw30056step3 = -raw30056step2 := by apply Matrix.ext; change ∀ i j, raw30056step3 i j = -(raw30056step2 i j); unfold raw30056step3 raw30056step2; decide +kernel
      have hl : raw30056step3Labels = raw30056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw30057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![2, 0, -2], ![3, -1, -2]]
def raw30057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-2, -1, 3], ![-3, 2, 1]]
def raw30057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30057step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30057 raw30057Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw30057 raw30057Labels = mixedMoment B raw30057step0 raw30057step0Labels := by
      have hz : ∀ j, raw30057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30057step0 = (fun i j => raw30057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30057step0 raw30057; decide +kernel
      have hl : raw30057step0Labels = raw30057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30057 raw30057Labels permutation434 hz
    mixedMoment B raw30057step0 raw30057step0Labels = mixedMoment B raw30057step1 raw30057step1Labels := by
      have hz : ∀ j, raw30057step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30057step1 = (fun i j => raw30057step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30057step1 raw30057step0; decide +kernel
      have hl : raw30057step1Labels = raw30057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30057step0 raw30057step0Labels permutation80 hz
    mixedMoment B raw30057step1 raw30057step1Labels = mixedMoment B raw30057step2 raw30057step2Labels := by
      have ha : raw30057step2 = (fun i j => raw30057step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30057step2 raw30057step1; decide +kernel
      have hl : raw30057step2Labels = raw30057step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30057step1 raw30057step1Labels permutation31 permutation2
    mixedMoment B raw30057step2 raw30057step2Labels = mixedMoment B raw30057step3 raw30057step3Labels := by
      have ha : raw30057step3 = -raw30057step2 := by apply Matrix.ext; change ∀ i j, raw30057step3 i j = -(raw30057step2 i j); unfold raw30057step3 raw30057step2; decide +kernel
      have hl : raw30057step3Labels = raw30057step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw30058 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![2, -2]]
def raw30058Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30058step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![0, 0], ![2, -2], ![2, -2]]
def raw30058step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30058step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]
def raw30058step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30058step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw30058step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30058 raw30058Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw30058 raw30058Labels = mixedMoment B raw30058step0 raw30058step0Labels := by
      have hz : ∀ j, raw30058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30058step0 = (fun i j => raw30058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30058step0 raw30058; decide +kernel
      have hl : raw30058step0Labels = raw30058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30058 raw30058Labels permutation434 hz
    mixedMoment B raw30058step0 raw30058step0Labels = mixedMoment B raw30058step1 raw30058step1Labels := by
      have hz : ∀ j, raw30058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30058step1 = (fun i j => raw30058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30058step1 raw30058step0; decide +kernel
      have hl : raw30058step1Labels = raw30058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30058step0 raw30058step0Labels permutation80 hz
    mixedMoment B raw30058step1 raw30058step1Labels = mixedMoment B raw30058step2 raw30058step2Labels := by
      have ha : raw30058step2 = (fun i j => raw30058step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30058step2 raw30058step1; decide +kernel
      have hl : raw30058step2Labels = raw30058step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30058step1 raw30058step1Labels permutation14 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw30059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30059 raw30059Labels = mixedMoment B node3042 node3042Labels := by
  calc
    mixedMoment B raw30059 raw30059Labels = mixedMoment B raw30059step0 raw30059step0Labels := by
      have hz : ∀ j, raw30059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30059step0 = (fun i j => raw30059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30059step0 raw30059; decide +kernel
      have hl : raw30059step0Labels = raw30059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30059 raw30059Labels permutation346 hz
    mixedMoment B raw30059step0 raw30059step0Labels = mixedMoment B raw30059step1 raw30059step1Labels := by
      have ha : raw30059step1 = (fun i j => raw30059step0 (permutation69 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30059step1 raw30059step0; decide +kernel
      have hl : raw30059step1Labels = raw30059step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30059step0 raw30059step0Labels permutation69 permutation4
    mixedMoment B raw30059step1 raw30059step1Labels = mixedMoment B raw30059step2 raw30059step2Labels := by
      have ha : raw30059step2 = -raw30059step1 := by apply Matrix.ext; change ∀ i j, raw30059step2 i j = -(raw30059step1 i j); unfold raw30059step2 raw30059step1; decide +kernel
      have hl : raw30059step2Labels = raw30059step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3042 node3042Labels := by rfl

def raw30060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30060 raw30060Labels = mixedMoment B node3695 node3695Labels := by
  calc
    mixedMoment B raw30060 raw30060Labels = mixedMoment B raw30060step0 raw30060step0Labels := by
      have ha : raw30060step0 = (fun i j => raw30060 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30060step0 raw30060; decide +kernel
      have hl : raw30060step0Labels = raw30060Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30060 raw30060Labels permutation587 permutation2
    mixedMoment B raw30060step0 raw30060step0Labels = mixedMoment B raw30060step1 raw30060step1Labels := by
      have ha : raw30060step1 = -raw30060step0 := by apply Matrix.ext; change ∀ i j, raw30060step1 i j = -(raw30060step0 i j); unfold raw30060step1 raw30060step0; decide +kernel
      have hl : raw30060step1Labels = raw30060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3695 node3695Labels := by rfl

def raw30061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30061 raw30061Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw30061 raw30061Labels = mixedMoment B raw30061step0 raw30061step0Labels := by
      have hz : ∀ j, raw30061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30061step0 = (fun i j => raw30061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30061step0 raw30061; decide +kernel
      have hl : raw30061step0Labels = raw30061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30061 raw30061Labels permutation346 hz
    mixedMoment B raw30061step0 raw30061step0Labels = mixedMoment B raw30061step1 raw30061step1Labels := by
      have ha : raw30061step1 = (fun i j => raw30061step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30061step1 raw30061step0; decide +kernel
      have hl : raw30061step1Labels = raw30061step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30061step0 raw30061step0Labels permutation125 permutation2
    mixedMoment B raw30061step1 raw30061step1Labels = mixedMoment B raw30061step2 raw30061step2Labels := by
      have ha : raw30061step2 = -raw30061step1 := by apply Matrix.ext; change ∀ i j, raw30061step2 i j = -(raw30061step1 i j); unfold raw30061step2 raw30061step1; decide +kernel
      have hl : raw30061step2Labels = raw30061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw30062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30062 raw30062Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw30062 raw30062Labels = mixedMoment B raw30062step0 raw30062step0Labels := by
      have hz : ∀ j, raw30062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30062step0 = (fun i j => raw30062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30062step0 raw30062; decide +kernel
      have hl : raw30062step0Labels = raw30062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30062 raw30062Labels permutation346 hz
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw30063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30063 raw30063Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw30063 raw30063Labels = mixedMoment B raw30063step0 raw30063step0Labels := by
      have hz : ∀ j, raw30063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30063step0 = (fun i j => raw30063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30063step0 raw30063; decide +kernel
      have hl : raw30063step0Labels = raw30063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30063 raw30063Labels permutation346 hz
    mixedMoment B raw30063step0 raw30063step0Labels = mixedMoment B raw30063step1 raw30063step1Labels := by
      have ha : raw30063step1 = (fun i j => raw30063step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30063step1 raw30063step0; decide +kernel
      have hl : raw30063step1Labels = raw30063step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30063step0 raw30063step0Labels permutation127 permutation2
    mixedMoment B raw30063step1 raw30063step1Labels = mixedMoment B raw30063step2 raw30063step2Labels := by
      have ha : raw30063step2 = -raw30063step1 := by apply Matrix.ext; change ∀ i j, raw30063step2 i j = -(raw30063step1 i j); unfold raw30063step2 raw30063step1; decide +kernel
      have hl : raw30063step2Labels = raw30063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw30064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw30064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw30064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30064 raw30064Labels = mixedMoment B node3041 node3041Labels := by
  calc
    mixedMoment B raw30064 raw30064Labels = mixedMoment B raw30064step0 raw30064step0Labels := by
      have ha : raw30064step0 = (fun i j => raw30064 (permutation324 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30064step0 raw30064; decide +kernel
      have hl : raw30064step0Labels = raw30064Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30064 raw30064Labels permutation324 permutation4
    mixedMoment B raw30064step0 raw30064step0Labels = mixedMoment B raw30064step1 raw30064step1Labels := by
      have ha : raw30064step1 = -raw30064step0 := by apply Matrix.ext; change ∀ i j, raw30064step1 i j = -(raw30064step0 i j); unfold raw30064step1 raw30064step0; decide +kernel
      have hl : raw30064step1Labels = raw30064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3041 node3041Labels := by rfl

def raw30065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30065 raw30065Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw30065 raw30065Labels = mixedMoment B raw30065step0 raw30065step0Labels := by
      have ha : raw30065step0 = (fun i j => raw30065 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30065step0 raw30065; decide +kernel
      have hl : raw30065step0Labels = raw30065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30065 raw30065Labels permutation587 permutation2
    mixedMoment B raw30065step0 raw30065step0Labels = mixedMoment B raw30065step1 raw30065step1Labels := by
      have ha : raw30065step1 = -raw30065step0 := by apply Matrix.ext; change ∀ i j, raw30065step1 i j = -(raw30065step0 i j); unfold raw30065step1 raw30065step0; decide +kernel
      have hl : raw30065step1Labels = raw30065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw30066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30066 raw30066Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw30066 raw30066Labels = mixedMoment B raw30066step0 raw30066step0Labels := by
      have ha : raw30066step0 = (fun i j => raw30066 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30066step0 raw30066; decide +kernel
      have hl : raw30066step0Labels = raw30066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30066 raw30066Labels permutation582 permutation2
    mixedMoment B raw30066step0 raw30066step0Labels = mixedMoment B raw30066step1 raw30066step1Labels := by
      have ha : raw30066step1 = -raw30066step0 := by apply Matrix.ext; change ∀ i j, raw30066step1 i j = -(raw30066step0 i j); unfold raw30066step1 raw30066step0; decide +kernel
      have hl : raw30066step1Labels = raw30066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw30067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30067 raw30067Labels = mixedMoment B node3869 node3869Labels := by
  calc
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw30068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30068 raw30068Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw30068 raw30068Labels = mixedMoment B raw30068step0 raw30068step0Labels := by
      have ha : raw30068step0 = (fun i j => raw30068 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30068step0 raw30068; decide +kernel
      have hl : raw30068step0Labels = raw30068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30068 raw30068Labels permutation584 permutation2
    mixedMoment B raw30068step0 raw30068step0Labels = mixedMoment B raw30068step1 raw30068step1Labels := by
      have ha : raw30068step1 = -raw30068step0 := by apply Matrix.ext; change ∀ i j, raw30068step1 i j = -(raw30068step0 i j); unfold raw30068step1 raw30068step0; decide +kernel
      have hl : raw30068step1Labels = raw30068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw30069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30069 raw30069Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw30069 raw30069Labels = mixedMoment B raw30069step0 raw30069step0Labels := by
      have ha : raw30069step0 = (fun i j => raw30069 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30069step0 raw30069; decide +kernel
      have hl : raw30069step0Labels = raw30069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30069 raw30069Labels permutation159 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

def raw30070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30070 raw30070Labels = mixedMoment B node3679 node3679Labels := by
  calc
    mixedMoment B raw30070 raw30070Labels = mixedMoment B raw30070step0 raw30070step0Labels := by
      have ha : raw30070step0 = (fun i j => raw30070 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30070step0 raw30070; decide +kernel
      have hl : raw30070step0Labels = raw30070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30070 raw30070Labels permutation584 permutation2
    mixedMoment B raw30070step0 raw30070step0Labels = mixedMoment B raw30070step1 raw30070step1Labels := by
      have ha : raw30070step1 = -raw30070step0 := by apply Matrix.ext; change ∀ i j, raw30070step1 i j = -(raw30070step0 i j); unfold raw30070step1 raw30070step0; decide +kernel
      have hl : raw30070step1Labels = raw30070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3679 node3679Labels := by rfl

def raw30071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30071 raw30071Labels = mixedMoment B node3695 node3695Labels := by
  calc
    mixedMoment B raw30071 raw30071Labels = mixedMoment B raw30071step0 raw30071step0Labels := by
      have ha : raw30071step0 = (fun i j => raw30071 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30071step0 raw30071; decide +kernel
      have hl : raw30071step0Labels = raw30071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30071 raw30071Labels permutation589 permutation2
    mixedMoment B raw30071step0 raw30071step0Labels = mixedMoment B raw30071step1 raw30071step1Labels := by
      have ha : raw30071step1 = -raw30071step0 := by apply Matrix.ext; change ∀ i j, raw30071step1 i j = -(raw30071step0 i j); unfold raw30071step1 raw30071step0; decide +kernel
      have hl : raw30071step1Labels = raw30071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3695 node3695Labels := by rfl

def raw30072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw30072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30072 raw30072Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw30072 raw30072Labels = mixedMoment B raw30072step0 raw30072step0Labels := by
      have ha : raw30072step0 = (fun i j => raw30072 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30072step0 raw30072; decide +kernel
      have hl : raw30072step0Labels = raw30072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30072 raw30072Labels permutation582 permutation2
    mixedMoment B raw30072step0 raw30072step0Labels = mixedMoment B raw30072step1 raw30072step1Labels := by
      have ha : raw30072step1 = -raw30072step0 := by apply Matrix.ext; change ∀ i j, raw30072step1 i j = -(raw30072step0 i j); unfold raw30072step1 raw30072step0; decide +kernel
      have hl : raw30072step1Labels = raw30072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw30073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw30073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30073 raw30073Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw30073 raw30073Labels = mixedMoment B raw30073step0 raw30073step0Labels := by
      have ha : raw30073step0 = (fun i j => raw30073 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30073step0 raw30073; decide +kernel
      have hl : raw30073step0Labels = raw30073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30073 raw30073Labels permutation158 permutation2
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw30074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw30074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30074 raw30074Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw30074 raw30074Labels = mixedMoment B raw30074step0 raw30074step0Labels := by
      have ha : raw30074step0 = (fun i j => raw30074 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30074step0 raw30074; decide +kernel
      have hl : raw30074step0Labels = raw30074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30074 raw30074Labels permutation584 permutation2
    mixedMoment B raw30074step0 raw30074step0Labels = mixedMoment B raw30074step1 raw30074step1Labels := by
      have ha : raw30074step1 = -raw30074step0 := by apply Matrix.ext; change ∀ i j, raw30074step1 i j = -(raw30074step0 i j); unfold raw30074step1 raw30074step0; decide +kernel
      have hl : raw30074step1Labels = raw30074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw30075 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw30075step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30075step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30075step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30075 raw30075Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30075 raw30075Labels = mixedMoment B raw30075step0 raw30075step0Labels := by
      have hz : ∀ j, raw30075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30075step0 = (fun i j => raw30075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30075step0 raw30075; decide +kernel
      have hl : raw30075step0Labels = raw30075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30075 raw30075Labels permutation265 hz
    mixedMoment B raw30075step0 raw30075step0Labels = mixedMoment B raw30075step1 raw30075step1Labels := by
      have ha : raw30075step1 = (fun i j => raw30075step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30075step1 raw30075step0; decide +kernel
      have hl : raw30075step1Labels = raw30075step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30075step0 raw30075step0Labels permutation39 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30076 raw30076Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw30076 raw30076Labels = mixedMoment B raw30076step0 raw30076step0Labels := by
      have hz : ∀ j, raw30076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30076step0 = (fun i j => raw30076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30076step0 raw30076; decide +kernel
      have hl : raw30076step0Labels = raw30076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30076 raw30076Labels permutation346 hz
    mixedMoment B raw30076step0 raw30076step0Labels = mixedMoment B raw30076step1 raw30076step1Labels := by
      have ha : raw30076step1 = (fun i j => raw30076step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30076step1 raw30076step0; decide +kernel
      have hl : raw30076step1Labels = raw30076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30076step0 raw30076step0Labels permutation127 permutation2
    mixedMoment B raw30076step1 raw30076step1Labels = mixedMoment B raw30076step2 raw30076step2Labels := by
      have ha : raw30076step2 = -raw30076step1 := by apply Matrix.ext; change ∀ i j, raw30076step2 i j = -(raw30076step1 i j); unfold raw30076step2 raw30076step1; decide +kernel
      have hl : raw30076step2Labels = raw30076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw30077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30077 raw30077Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw30077 raw30077Labels = mixedMoment B raw30077step0 raw30077step0Labels := by
      have ha : raw30077step0 = (fun i j => raw30077 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30077step0 raw30077; decide +kernel
      have hl : raw30077step0Labels = raw30077Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30077 raw30077Labels permutation587 permutation2
    mixedMoment B raw30077step0 raw30077step0Labels = mixedMoment B raw30077step1 raw30077step1Labels := by
      have ha : raw30077step1 = -raw30077step0 := by apply Matrix.ext; change ∀ i j, raw30077step1 i j = -(raw30077step0 i j); unfold raw30077step1 raw30077step0; decide +kernel
      have hl : raw30077step1Labels = raw30077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw30078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30078 raw30078Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30078 raw30078Labels = mixedMoment B raw30078step0 raw30078step0Labels := by
      have hz : ∀ j, raw30078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30078step0 = (fun i j => raw30078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30078step0 raw30078; decide +kernel
      have hl : raw30078step0Labels = raw30078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30078 raw30078Labels permutation346 hz
    mixedMoment B raw30078step0 raw30078step0Labels = mixedMoment B raw30078step1 raw30078step1Labels := by
      have ha : raw30078step1 = (fun i j => raw30078step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30078step1 raw30078step0; decide +kernel
      have hl : raw30078step1Labels = raw30078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30078step0 raw30078step0Labels permutation125 permutation2
    mixedMoment B raw30078step1 raw30078step1Labels = mixedMoment B raw30078step2 raw30078step2Labels := by
      have ha : raw30078step2 = -raw30078step1 := by apply Matrix.ext; change ∀ i j, raw30078step2 i j = -(raw30078step1 i j); unfold raw30078step2 raw30078step1; decide +kernel
      have hl : raw30078step2Labels = raw30078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw30079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30079 raw30079Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw30079 raw30079Labels = mixedMoment B raw30079step0 raw30079step0Labels := by
      have hz : ∀ j, raw30079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30079step0 = (fun i j => raw30079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30079step0 raw30079; decide +kernel
      have hl : raw30079step0Labels = raw30079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30079 raw30079Labels permutation346 hz
    mixedMoment B raw30079step0 raw30079step0Labels = mixedMoment B raw30079step1 raw30079step1Labels := by
      have ha : raw30079step1 = (fun i j => raw30079step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30079step1 raw30079step0; decide +kernel
      have hl : raw30079step1Labels = raw30079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30079step0 raw30079step0Labels permutation127 permutation2
    mixedMoment B raw30079step1 raw30079step1Labels = mixedMoment B raw30079step2 raw30079step2Labels := by
      have ha : raw30079step2 = -raw30079step1 := by apply Matrix.ext; change ∀ i j, raw30079step2 i j = -(raw30079step1 i j); unfold raw30079step2 raw30079step1; decide +kernel
      have hl : raw30079step2Labels = raw30079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
