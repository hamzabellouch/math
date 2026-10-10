import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23424 raw23424Labels = mixedMoment B node926 node926Labels := by
  calc
    mixedMoment B raw23424 raw23424Labels = mixedMoment B raw23424step0 raw23424step0Labels := by
      have hz : ∀ j, raw23424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23424step0 = (fun i j => raw23424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23424step0 raw23424; decide +kernel
      have hl : raw23424step0Labels = raw23424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23424 raw23424Labels permutation346 hz
    mixedMoment B raw23424step0 raw23424step0Labels = mixedMoment B raw23424step1 raw23424step1Labels := by
      have ha : raw23424step1 = (fun i j => raw23424step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23424step1 raw23424step0; decide +kernel
      have hl : raw23424step1Labels = raw23424step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23424step0 raw23424step0Labels permutation39 permutation2
    _ = mixedMoment B node926 node926Labels := by rfl

def raw23425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23425 raw23425Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw23425 raw23425Labels = mixedMoment B raw23425step0 raw23425step0Labels := by
      have hz : ∀ j, raw23425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23425step0 = (fun i j => raw23425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23425step0 raw23425; decide +kernel
      have hl : raw23425step0Labels = raw23425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23425 raw23425Labels permutation434 hz
    mixedMoment B raw23425step0 raw23425step0Labels = mixedMoment B raw23425step1 raw23425step1Labels := by
      have hz : ∀ j, raw23425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23425step1 = (fun i j => raw23425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23425step1 raw23425step0; decide +kernel
      have hl : raw23425step1Labels = raw23425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23425step0 raw23425step0Labels permutation80 hz
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw23426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23426 raw23426Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw23426 raw23426Labels = mixedMoment B raw23426step0 raw23426step0Labels := by
      have hz : ∀ j, raw23426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23426step0 = (fun i j => raw23426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23426step0 raw23426; decide +kernel
      have hl : raw23426step0Labels = raw23426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23426 raw23426Labels permutation434 hz
    mixedMoment B raw23426step0 raw23426step0Labels = mixedMoment B raw23426step1 raw23426step1Labels := by
      have hz : ∀ j, raw23426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23426step1 = (fun i j => raw23426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23426step1 raw23426step0; decide +kernel
      have hl : raw23426step1Labels = raw23426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23426step0 raw23426step0Labels permutation80 hz
    mixedMoment B raw23426step1 raw23426step1Labels = mixedMoment B raw23426step2 raw23426step2Labels := by
      have ha : raw23426step2 = (fun i j => raw23426step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23426step2 raw23426step1; decide +kernel
      have hl : raw23426step2Labels = raw23426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23426step1 raw23426step1Labels permutation9 permutation2
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw23427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23427step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23427step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23427 raw23427Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw23427 raw23427Labels = mixedMoment B raw23427step0 raw23427step0Labels := by
      have hz : ∀ j, raw23427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23427step0 = (fun i j => raw23427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23427step0 raw23427; decide +kernel
      have hl : raw23427step0Labels = raw23427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23427 raw23427Labels permutation434 hz
    mixedMoment B raw23427step0 raw23427step0Labels = mixedMoment B raw23427step1 raw23427step1Labels := by
      have hz : ∀ j, raw23427step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23427step1 = (fun i j => raw23427step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23427step1 raw23427step0; decide +kernel
      have hl : raw23427step1Labels = raw23427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23427step0 raw23427step0Labels permutation80 hz
    mixedMoment B raw23427step1 raw23427step1Labels = mixedMoment B raw23427step2 raw23427step2Labels := by
      have ha : raw23427step2 = (fun i j => raw23427step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23427step2 raw23427step1; decide +kernel
      have hl : raw23427step2Labels = raw23427step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23427step1 raw23427step1Labels permutation9 permutation3
    mixedMoment B raw23427step2 raw23427step2Labels = mixedMoment B raw23427step3 raw23427step3Labels := by
      have ha : raw23427step3 = raw23427step2 := by apply Matrix.ext; unfold raw23427step3 raw23427step2; decide +kernel
      have hl : raw23427step2Labels = labelEmbedding6 ∘ raw23427step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23427step2 raw23427step2Labels raw23427step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw23428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23428step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23428 raw23428Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23428 raw23428Labels = mixedMoment B raw23428step0 raw23428step0Labels := by
      have hz : ∀ j, raw23428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23428step0 = (fun i j => raw23428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23428step0 raw23428; decide +kernel
      have hl : raw23428step0Labels = raw23428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23428 raw23428Labels permutation434 hz
    mixedMoment B raw23428step0 raw23428step0Labels = mixedMoment B raw23428step1 raw23428step1Labels := by
      have ha : raw23428step1 = (fun i j => raw23428step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23428step1 raw23428step0; decide +kernel
      have hl : raw23428step1Labels = raw23428step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23428step0 raw23428step0Labels permutation39 permutation3
    mixedMoment B raw23428step1 raw23428step1Labels = mixedMoment B raw23428step2 raw23428step2Labels := by
      have ha : raw23428step2 = raw23428step1 := by apply Matrix.ext; unfold raw23428step2 raw23428step1; decide +kernel
      have hl : raw23428step1Labels = labelEmbedding6 ∘ raw23428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23428step1 raw23428step1Labels raw23428step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23429step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23429 raw23429Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23429 raw23429Labels = mixedMoment B raw23429step0 raw23429step0Labels := by
      have hz : ∀ j, raw23429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23429step0 = (fun i j => raw23429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23429step0 raw23429; decide +kernel
      have hl : raw23429step0Labels = raw23429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23429 raw23429Labels permutation346 hz
    mixedMoment B raw23429step0 raw23429step0Labels = mixedMoment B raw23429step1 raw23429step1Labels := by
      have ha : raw23429step1 = (fun i j => raw23429step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23429step1 raw23429step0; decide +kernel
      have hl : raw23429step1Labels = raw23429step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23429step0 raw23429step0Labels permutation39 permutation3
    mixedMoment B raw23429step1 raw23429step1Labels = mixedMoment B raw23429step2 raw23429step2Labels := by
      have ha : raw23429step2 = raw23429step1 := by apply Matrix.ext; unfold raw23429step2 raw23429step1; decide +kernel
      have hl : raw23429step1Labels = labelEmbedding6 ∘ raw23429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23429step1 raw23429step1Labels raw23429step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23430step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23430step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23430 raw23430Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw23430 raw23430Labels = mixedMoment B raw23430step0 raw23430step0Labels := by
      have hz : ∀ j, raw23430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23430step0 = (fun i j => raw23430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23430step0 raw23430; decide +kernel
      have hl : raw23430step0Labels = raw23430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23430 raw23430Labels permutation434 hz
    mixedMoment B raw23430step0 raw23430step0Labels = mixedMoment B raw23430step1 raw23430step1Labels := by
      have hz : ∀ j, raw23430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23430step1 = (fun i j => raw23430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23430step1 raw23430step0; decide +kernel
      have hl : raw23430step1Labels = raw23430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23430step0 raw23430step0Labels permutation80 hz
    mixedMoment B raw23430step1 raw23430step1Labels = mixedMoment B raw23430step2 raw23430step2Labels := by
      have ha : raw23430step2 = (fun i j => raw23430step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23430step2 raw23430step1; decide +kernel
      have hl : raw23430step2Labels = raw23430step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23430step1 raw23430step1Labels permutation12 permutation3
    mixedMoment B raw23430step2 raw23430step2Labels = mixedMoment B raw23430step3 raw23430step3Labels := by
      have ha : raw23430step3 = raw23430step2 := by apply Matrix.ext; unfold raw23430step3 raw23430step2; decide +kernel
      have hl : raw23430step2Labels = labelEmbedding6 ∘ raw23430step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23430step2 raw23430step2Labels raw23430step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw23431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23431step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23431 raw23431Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw23431 raw23431Labels = mixedMoment B raw23431step0 raw23431step0Labels := by
      have hz : ∀ j, raw23431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23431step0 = (fun i j => raw23431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23431step0 raw23431; decide +kernel
      have hl : raw23431step0Labels = raw23431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23431 raw23431Labels permutation434 hz
    mixedMoment B raw23431step0 raw23431step0Labels = mixedMoment B raw23431step1 raw23431step1Labels := by
      have hz : ∀ j, raw23431step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23431step1 = (fun i j => raw23431step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23431step1 raw23431step0; decide +kernel
      have hl : raw23431step1Labels = raw23431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23431step0 raw23431step0Labels permutation56 hz
    mixedMoment B raw23431step1 raw23431step1Labels = mixedMoment B raw23431step2 raw23431step2Labels := by
      have ha : raw23431step2 = (fun i j => raw23431step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23431step2 raw23431step1; decide +kernel
      have hl : raw23431step2Labels = raw23431step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23431step1 raw23431step1Labels permutation9 permutation3
    mixedMoment B raw23431step2 raw23431step2Labels = mixedMoment B raw23431step3 raw23431step3Labels := by
      have ha : raw23431step3 = raw23431step2 := by apply Matrix.ext; unfold raw23431step3 raw23431step2; decide +kernel
      have hl : raw23431step2Labels = labelEmbedding6 ∘ raw23431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23431step2 raw23431step2Labels raw23431step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw23432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23432step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23432 raw23432Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23432 raw23432Labels = mixedMoment B raw23432step0 raw23432step0Labels := by
      have hz : ∀ j, raw23432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23432step0 = (fun i j => raw23432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23432step0 raw23432; decide +kernel
      have hl : raw23432step0Labels = raw23432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23432 raw23432Labels permutation434 hz
    mixedMoment B raw23432step0 raw23432step0Labels = mixedMoment B raw23432step1 raw23432step1Labels := by
      have ha : raw23432step1 = (fun i j => raw23432step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23432step1 raw23432step0; decide +kernel
      have hl : raw23432step1Labels = raw23432step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23432step0 raw23432step0Labels permutation33 permutation3
    mixedMoment B raw23432step1 raw23432step1Labels = mixedMoment B raw23432step2 raw23432step2Labels := by
      have ha : raw23432step2 = raw23432step1 := by apply Matrix.ext; unfold raw23432step2 raw23432step1; decide +kernel
      have hl : raw23432step1Labels = labelEmbedding6 ∘ raw23432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23432step1 raw23432step1Labels raw23432step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23433step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23433 raw23433Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23433 raw23433Labels = mixedMoment B raw23433step0 raw23433step0Labels := by
      have hz : ∀ j, raw23433 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23433step0 = (fun i j => raw23433 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23433step0 raw23433; decide +kernel
      have hl : raw23433step0Labels = raw23433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23433 raw23433Labels permutation265 hz
    mixedMoment B raw23433step0 raw23433step0Labels = mixedMoment B raw23433step1 raw23433step1Labels := by
      have ha : raw23433step1 = (fun i j => raw23433step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23433step1 raw23433step0; decide +kernel
      have hl : raw23433step1Labels = raw23433step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23433step0 raw23433step0Labels permutation39 permutation3
    mixedMoment B raw23433step1 raw23433step1Labels = mixedMoment B raw23433step2 raw23433step2Labels := by
      have ha : raw23433step2 = raw23433step1 := by apply Matrix.ext; unfold raw23433step2 raw23433step1; decide +kernel
      have hl : raw23433step1Labels = labelEmbedding6 ∘ raw23433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23433step1 raw23433step1Labels raw23433step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23434step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23434 raw23434Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw23434 raw23434Labels = mixedMoment B raw23434step0 raw23434step0Labels := by
      have hz : ∀ j, raw23434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23434step0 = (fun i j => raw23434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23434step0 raw23434; decide +kernel
      have hl : raw23434step0Labels = raw23434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23434 raw23434Labels permutation434 hz
    mixedMoment B raw23434step0 raw23434step0Labels = mixedMoment B raw23434step1 raw23434step1Labels := by
      have hz : ∀ j, raw23434step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23434step1 = (fun i j => raw23434step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23434step1 raw23434step0; decide +kernel
      have hl : raw23434step1Labels = raw23434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23434step0 raw23434step0Labels permutation56 hz
    mixedMoment B raw23434step1 raw23434step1Labels = mixedMoment B raw23434step2 raw23434step2Labels := by
      have ha : raw23434step2 = (fun i j => raw23434step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23434step2 raw23434step1; decide +kernel
      have hl : raw23434step2Labels = raw23434step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23434step1 raw23434step1Labels permutation12 permutation3
    mixedMoment B raw23434step2 raw23434step2Labels = mixedMoment B raw23434step3 raw23434step3Labels := by
      have ha : raw23434step3 = raw23434step2 := by apply Matrix.ext; unfold raw23434step3 raw23434step2; decide +kernel
      have hl : raw23434step2Labels = labelEmbedding6 ∘ raw23434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23434step2 raw23434step2Labels raw23434step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw23435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23435step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23435step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23435 raw23435Labels = mixedMoment B node4129 node4129Labels := by
  calc
    mixedMoment B raw23435 raw23435Labels = mixedMoment B raw23435step0 raw23435step0Labels := by
      have hz : ∀ j, raw23435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23435step0 = (fun i j => raw23435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23435step0 raw23435; decide +kernel
      have hl : raw23435step0Labels = raw23435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23435 raw23435Labels permutation346 hz
    mixedMoment B raw23435step0 raw23435step0Labels = mixedMoment B raw23435step1 raw23435step1Labels := by
      have hz : ∀ j, raw23435step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23435step1 = (fun i j => raw23435step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23435step1 raw23435step0; decide +kernel
      have hl : raw23435step1Labels = raw23435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23435step0 raw23435step0Labels permutation56 hz
    mixedMoment B raw23435step1 raw23435step1Labels = mixedMoment B raw23435step2 raw23435step2Labels := by
      have ha : raw23435step2 = (fun i j => raw23435step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23435step2 raw23435step1; decide +kernel
      have hl : raw23435step2Labels = raw23435step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23435step1 raw23435step1Labels permutation9 permutation3
    mixedMoment B raw23435step2 raw23435step2Labels = mixedMoment B raw23435step3 raw23435step3Labels := by
      have ha : raw23435step3 = raw23435step2 := by apply Matrix.ext; unfold raw23435step3 raw23435step2; decide +kernel
      have hl : raw23435step2Labels = labelEmbedding6 ∘ raw23435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23435step2 raw23435step2Labels raw23435step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4129 node4129Labels := by rfl

def raw23436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23436 raw23436Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23436 raw23436Labels = mixedMoment B raw23436step0 raw23436step0Labels := by
      have hz : ∀ j, raw23436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23436step0 = (fun i j => raw23436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23436step0 raw23436; decide +kernel
      have hl : raw23436step0Labels = raw23436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23436 raw23436Labels permutation346 hz
    mixedMoment B raw23436step0 raw23436step0Labels = mixedMoment B raw23436step1 raw23436step1Labels := by
      have ha : raw23436step1 = (fun i j => raw23436step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23436step1 raw23436step0; decide +kernel
      have hl : raw23436step1Labels = raw23436step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23436step0 raw23436step0Labels permutation33 permutation3
    mixedMoment B raw23436step1 raw23436step1Labels = mixedMoment B raw23436step2 raw23436step2Labels := by
      have ha : raw23436step2 = raw23436step1 := by apply Matrix.ext; unfold raw23436step2 raw23436step1; decide +kernel
      have hl : raw23436step1Labels = labelEmbedding6 ∘ raw23436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23436step1 raw23436step1Labels raw23436step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23437 raw23437Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw23437 raw23437Labels = mixedMoment B raw23437step0 raw23437step0Labels := by
      have hz : ∀ j, raw23437 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23437step0 = (fun i j => raw23437 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23437step0 raw23437; decide +kernel
      have hl : raw23437step0Labels = raw23437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23437 raw23437Labels permutation265 hz
    mixedMoment B raw23437step0 raw23437step0Labels = mixedMoment B raw23437step1 raw23437step1Labels := by
      have ha : raw23437step1 = (fun i j => raw23437step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23437step1 raw23437step0; decide +kernel
      have hl : raw23437step1Labels = raw23437step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23437step0 raw23437step0Labels permutation33 permutation3
    mixedMoment B raw23437step1 raw23437step1Labels = mixedMoment B raw23437step2 raw23437step2Labels := by
      have ha : raw23437step2 = raw23437step1 := by apply Matrix.ext; unfold raw23437step2 raw23437step1; decide +kernel
      have hl : raw23437step1Labels = labelEmbedding6 ∘ raw23437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23437step1 raw23437step1Labels raw23437step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw23438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23438step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23438step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23438 raw23438Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw23438 raw23438Labels = mixedMoment B raw23438step0 raw23438step0Labels := by
      have hz : ∀ j, raw23438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23438step0 = (fun i j => raw23438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23438step0 raw23438; decide +kernel
      have hl : raw23438step0Labels = raw23438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23438 raw23438Labels permutation346 hz
    mixedMoment B raw23438step0 raw23438step0Labels = mixedMoment B raw23438step1 raw23438step1Labels := by
      have hz : ∀ j, raw23438step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23438step1 = (fun i j => raw23438step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23438step1 raw23438step0; decide +kernel
      have hl : raw23438step1Labels = raw23438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23438step0 raw23438step0Labels permutation56 hz
    mixedMoment B raw23438step1 raw23438step1Labels = mixedMoment B raw23438step2 raw23438step2Labels := by
      have ha : raw23438step2 = (fun i j => raw23438step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23438step2 raw23438step1; decide +kernel
      have hl : raw23438step2Labels = raw23438step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23438step1 raw23438step1Labels permutation12 permutation3
    mixedMoment B raw23438step2 raw23438step2Labels = mixedMoment B raw23438step3 raw23438step3Labels := by
      have ha : raw23438step3 = raw23438step2 := by apply Matrix.ext; unfold raw23438step3 raw23438step2; decide +kernel
      have hl : raw23438step2Labels = labelEmbedding6 ∘ raw23438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23438step2 raw23438step2Labels raw23438step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw23439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23439step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![3, -4, 1], ![2, 0, -2]]
def raw23439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23439step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw23439step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23439step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw23439step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23439 raw23439Labels = mixedMoment B node4135 node4135Labels := by
  calc
    mixedMoment B raw23439 raw23439Labels = mixedMoment B raw23439step0 raw23439step0Labels := by
      have hz : ∀ j, raw23439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23439step0 = (fun i j => raw23439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23439step0 raw23439; decide +kernel
      have hl : raw23439step0Labels = raw23439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23439 raw23439Labels permutation434 hz
    mixedMoment B raw23439step0 raw23439step0Labels = mixedMoment B raw23439step1 raw23439step1Labels := by
      have hz : ∀ j, raw23439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23439step1 = (fun i j => raw23439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23439step1 raw23439step0; decide +kernel
      have hl : raw23439step1Labels = raw23439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23439step0 raw23439step0Labels permutation80 hz
    mixedMoment B raw23439step1 raw23439step1Labels = mixedMoment B raw23439step2 raw23439step2Labels := by
      have hz : ∀ j, raw23439step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23439step2 = (fun i j => raw23439step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23439step2 raw23439step1; decide +kernel
      have hl : raw23439step2Labels = raw23439step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23439step1 raw23439step1Labels permutation14 hz
    mixedMoment B raw23439step2 raw23439step2Labels = mixedMoment B raw23439step3 raw23439step3Labels := by
      have ha : raw23439step3 = (fun i j => raw23439step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23439step3 raw23439step2; decide +kernel
      have hl : raw23439step3Labels = raw23439step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23439step2 raw23439step2Labels permutation3 permutation3
    mixedMoment B raw23439step3 raw23439step3Labels = mixedMoment B raw23439step4 raw23439step4Labels := by
      have ha : raw23439step4 = raw23439step3 := by apply Matrix.ext; unfold raw23439step4 raw23439step3; decide +kernel
      have hl : raw23439step3Labels = labelEmbedding6 ∘ raw23439step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23439step3 raw23439step3Labels raw23439step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4135 node4135Labels := by rfl

def raw23440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23440step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23440step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23440 raw23440Labels = mixedMoment B node4316 node4316Labels := by
  calc
    mixedMoment B raw23440 raw23440Labels = mixedMoment B raw23440step0 raw23440step0Labels := by
      have hz : ∀ j, raw23440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23440step0 = (fun i j => raw23440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23440step0 raw23440; decide +kernel
      have hl : raw23440step0Labels = raw23440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23440 raw23440Labels permutation434 hz
    mixedMoment B raw23440step0 raw23440step0Labels = mixedMoment B raw23440step1 raw23440step1Labels := by
      have hz : ∀ j, raw23440step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23440step1 = (fun i j => raw23440step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23440step1 raw23440step0; decide +kernel
      have hl : raw23440step1Labels = raw23440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23440step0 raw23440step0Labels permutation80 hz
    mixedMoment B raw23440step1 raw23440step1Labels = mixedMoment B raw23440step2 raw23440step2Labels := by
      have ha : raw23440step2 = (fun i j => raw23440step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23440step2 raw23440step1; decide +kernel
      have hl : raw23440step2Labels = raw23440step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23440step1 raw23440step1Labels permutation9 permutation3
    mixedMoment B raw23440step2 raw23440step2Labels = mixedMoment B raw23440step3 raw23440step3Labels := by
      have ha : raw23440step3 = raw23440step2 := by apply Matrix.ext; unfold raw23440step3 raw23440step2; decide +kernel
      have hl : raw23440step2Labels = labelEmbedding6 ∘ raw23440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23440step2 raw23440step2Labels raw23440step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4316 node4316Labels := by rfl

def raw23441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23441step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23441step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23441 raw23441Labels = mixedMoment B node4316 node4316Labels := by
  calc
    mixedMoment B raw23441 raw23441Labels = mixedMoment B raw23441step0 raw23441step0Labels := by
      have hz : ∀ j, raw23441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23441step0 = (fun i j => raw23441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23441step0 raw23441; decide +kernel
      have hl : raw23441step0Labels = raw23441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23441 raw23441Labels permutation434 hz
    mixedMoment B raw23441step0 raw23441step0Labels = mixedMoment B raw23441step1 raw23441step1Labels := by
      have hz : ∀ j, raw23441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23441step1 = (fun i j => raw23441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23441step1 raw23441step0; decide +kernel
      have hl : raw23441step1Labels = raw23441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23441step0 raw23441step0Labels permutation56 hz
    mixedMoment B raw23441step1 raw23441step1Labels = mixedMoment B raw23441step2 raw23441step2Labels := by
      have ha : raw23441step2 = (fun i j => raw23441step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23441step2 raw23441step1; decide +kernel
      have hl : raw23441step2Labels = raw23441step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23441step1 raw23441step1Labels permutation9 permutation3
    mixedMoment B raw23441step2 raw23441step2Labels = mixedMoment B raw23441step3 raw23441step3Labels := by
      have ha : raw23441step3 = raw23441step2 := by apply Matrix.ext; unfold raw23441step3 raw23441step2; decide +kernel
      have hl : raw23441step2Labels = labelEmbedding6 ∘ raw23441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23441step2 raw23441step2Labels raw23441step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4316 node4316Labels := by rfl

def raw23442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23442step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23442step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23442step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23442 raw23442Labels = mixedMoment B node4316 node4316Labels := by
  calc
    mixedMoment B raw23442 raw23442Labels = mixedMoment B raw23442step0 raw23442step0Labels := by
      have hz : ∀ j, raw23442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23442step0 = (fun i j => raw23442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23442step0 raw23442; decide +kernel
      have hl : raw23442step0Labels = raw23442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23442 raw23442Labels permutation346 hz
    mixedMoment B raw23442step0 raw23442step0Labels = mixedMoment B raw23442step1 raw23442step1Labels := by
      have hz : ∀ j, raw23442step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23442step1 = (fun i j => raw23442step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23442step1 raw23442step0; decide +kernel
      have hl : raw23442step1Labels = raw23442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23442step0 raw23442step0Labels permutation56 hz
    mixedMoment B raw23442step1 raw23442step1Labels = mixedMoment B raw23442step2 raw23442step2Labels := by
      have ha : raw23442step2 = (fun i j => raw23442step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23442step2 raw23442step1; decide +kernel
      have hl : raw23442step2Labels = raw23442step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23442step1 raw23442step1Labels permutation9 permutation3
    mixedMoment B raw23442step2 raw23442step2Labels = mixedMoment B raw23442step3 raw23442step3Labels := by
      have ha : raw23442step3 = raw23442step2 := by apply Matrix.ext; unfold raw23442step3 raw23442step2; decide +kernel
      have hl : raw23442step2Labels = labelEmbedding6 ∘ raw23442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23442step2 raw23442step2Labels raw23442step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4316 node4316Labels := by rfl

def raw23443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23443step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![3, -4, 1], ![1, 1, -2]]
def raw23443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23443step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw23443step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23443step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw23443step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23443 raw23443Labels = mixedMoment B node4493 node4493Labels := by
  calc
    mixedMoment B raw23443 raw23443Labels = mixedMoment B raw23443step0 raw23443step0Labels := by
      have hz : ∀ j, raw23443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23443step0 = (fun i j => raw23443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23443step0 raw23443; decide +kernel
      have hl : raw23443step0Labels = raw23443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23443 raw23443Labels permutation434 hz
    mixedMoment B raw23443step0 raw23443step0Labels = mixedMoment B raw23443step1 raw23443step1Labels := by
      have hz : ∀ j, raw23443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23443step1 = (fun i j => raw23443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23443step1 raw23443step0; decide +kernel
      have hl : raw23443step1Labels = raw23443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23443step0 raw23443step0Labels permutation80 hz
    mixedMoment B raw23443step1 raw23443step1Labels = mixedMoment B raw23443step2 raw23443step2Labels := by
      have hz : ∀ j, raw23443step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23443step2 = (fun i j => raw23443step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23443step2 raw23443step1; decide +kernel
      have hl : raw23443step2Labels = raw23443step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23443step1 raw23443step1Labels permutation14 hz
    mixedMoment B raw23443step2 raw23443step2Labels = mixedMoment B raw23443step3 raw23443step3Labels := by
      have ha : raw23443step3 = (fun i j => raw23443step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23443step3 raw23443step2; decide +kernel
      have hl : raw23443step3Labels = raw23443step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23443step2 raw23443step2Labels permutation3 permutation3
    mixedMoment B raw23443step3 raw23443step3Labels = mixedMoment B raw23443step4 raw23443step4Labels := by
      have ha : raw23443step4 = raw23443step3 := by apply Matrix.ext; unfold raw23443step4 raw23443step3; decide +kernel
      have hl : raw23443step3Labels = labelEmbedding6 ∘ raw23443step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23443step3 raw23443step3Labels raw23443step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4493 node4493Labels := by rfl

def raw23444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23444step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23444 raw23444Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw23444 raw23444Labels = mixedMoment B raw23444step0 raw23444step0Labels := by
      have hz : ∀ j, raw23444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23444step0 = (fun i j => raw23444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23444step0 raw23444; decide +kernel
      have hl : raw23444step0Labels = raw23444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23444 raw23444Labels permutation434 hz
    mixedMoment B raw23444step0 raw23444step0Labels = mixedMoment B raw23444step1 raw23444step1Labels := by
      have hz : ∀ j, raw23444step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23444step1 = (fun i j => raw23444step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23444step1 raw23444step0; decide +kernel
      have hl : raw23444step1Labels = raw23444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23444step0 raw23444step0Labels permutation80 hz
    mixedMoment B raw23444step1 raw23444step1Labels = mixedMoment B raw23444step2 raw23444step2Labels := by
      have ha : raw23444step2 = (fun i j => raw23444step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23444step2 raw23444step1; decide +kernel
      have hl : raw23444step2Labels = raw23444step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23444step1 raw23444step1Labels permutation9 permutation3
    _ = mixedMoment B node560 node560Labels := by rfl

def raw23445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23445 raw23445Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23445 raw23445Labels = mixedMoment B raw23445step0 raw23445step0Labels := by
      have hz : ∀ j, raw23445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23445step0 = (fun i j => raw23445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23445step0 raw23445; decide +kernel
      have hl : raw23445step0Labels = raw23445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23445 raw23445Labels permutation434 hz
    mixedMoment B raw23445step0 raw23445step0Labels = mixedMoment B raw23445step1 raw23445step1Labels := by
      have ha : raw23445step1 = (fun i j => raw23445step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23445step1 raw23445step0; decide +kernel
      have hl : raw23445step1Labels = raw23445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23445step0 raw23445step0Labels permutation39 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23446 raw23446Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23446 raw23446Labels = mixedMoment B raw23446step0 raw23446step0Labels := by
      have hz : ∀ j, raw23446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23446step0 = (fun i j => raw23446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23446step0 raw23446; decide +kernel
      have hl : raw23446step0Labels = raw23446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23446 raw23446Labels permutation346 hz
    mixedMoment B raw23446step0 raw23446step0Labels = mixedMoment B raw23446step1 raw23446step1Labels := by
      have ha : raw23446step1 = (fun i j => raw23446step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23446step1 raw23446step0; decide +kernel
      have hl : raw23446step1Labels = raw23446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23446step0 raw23446step0Labels permutation39 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23447 raw23447Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw23447 raw23447Labels = mixedMoment B raw23447step0 raw23447step0Labels := by
      have hz : ∀ j, raw23447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23447step0 = (fun i j => raw23447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23447step0 raw23447; decide +kernel
      have hl : raw23447step0Labels = raw23447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23447 raw23447Labels permutation434 hz
    mixedMoment B raw23447step0 raw23447step0Labels = mixedMoment B raw23447step1 raw23447step1Labels := by
      have hz : ∀ j, raw23447step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23447step1 = (fun i j => raw23447step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23447step1 raw23447step0; decide +kernel
      have hl : raw23447step1Labels = raw23447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23447step0 raw23447step0Labels permutation80 hz
    mixedMoment B raw23447step1 raw23447step1Labels = mixedMoment B raw23447step2 raw23447step2Labels := by
      have ha : raw23447step2 = (fun i j => raw23447step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23447step2 raw23447step1; decide +kernel
      have hl : raw23447step2Labels = raw23447step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23447step1 raw23447step1Labels permutation12 permutation3
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw23448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23448step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23448step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23448 raw23448Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw23448 raw23448Labels = mixedMoment B raw23448step0 raw23448step0Labels := by
      have hz : ∀ j, raw23448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23448step0 = (fun i j => raw23448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23448step0 raw23448; decide +kernel
      have hl : raw23448step0Labels = raw23448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23448 raw23448Labels permutation434 hz
    mixedMoment B raw23448step0 raw23448step0Labels = mixedMoment B raw23448step1 raw23448step1Labels := by
      have hz : ∀ j, raw23448step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23448step1 = (fun i j => raw23448step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23448step1 raw23448step0; decide +kernel
      have hl : raw23448step1Labels = raw23448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23448step0 raw23448step0Labels permutation56 hz
    mixedMoment B raw23448step1 raw23448step1Labels = mixedMoment B raw23448step2 raw23448step2Labels := by
      have ha : raw23448step2 = (fun i j => raw23448step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23448step2 raw23448step1; decide +kernel
      have hl : raw23448step2Labels = raw23448step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23448step1 raw23448step1Labels permutation9 permutation3
    _ = mixedMoment B node560 node560Labels := by rfl

def raw23449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23449 raw23449Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23449 raw23449Labels = mixedMoment B raw23449step0 raw23449step0Labels := by
      have hz : ∀ j, raw23449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23449step0 = (fun i j => raw23449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23449step0 raw23449; decide +kernel
      have hl : raw23449step0Labels = raw23449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23449 raw23449Labels permutation434 hz
    mixedMoment B raw23449step0 raw23449step0Labels = mixedMoment B raw23449step1 raw23449step1Labels := by
      have ha : raw23449step1 = (fun i j => raw23449step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23449step1 raw23449step0; decide +kernel
      have hl : raw23449step1Labels = raw23449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23449step0 raw23449step0Labels permutation33 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23450 raw23450Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23450 raw23450Labels = mixedMoment B raw23450step0 raw23450step0Labels := by
      have hz : ∀ j, raw23450 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23450step0 = (fun i j => raw23450 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23450step0 raw23450; decide +kernel
      have hl : raw23450step0Labels = raw23450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23450 raw23450Labels permutation265 hz
    mixedMoment B raw23450step0 raw23450step0Labels = mixedMoment B raw23450step1 raw23450step1Labels := by
      have ha : raw23450step1 = (fun i j => raw23450step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23450step1 raw23450step0; decide +kernel
      have hl : raw23450step1Labels = raw23450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23450step0 raw23450step0Labels permutation39 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23451step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23451step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23451 raw23451Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw23451 raw23451Labels = mixedMoment B raw23451step0 raw23451step0Labels := by
      have hz : ∀ j, raw23451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23451step0 = (fun i j => raw23451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23451step0 raw23451; decide +kernel
      have hl : raw23451step0Labels = raw23451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23451 raw23451Labels permutation434 hz
    mixedMoment B raw23451step0 raw23451step0Labels = mixedMoment B raw23451step1 raw23451step1Labels := by
      have hz : ∀ j, raw23451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23451step1 = (fun i j => raw23451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23451step1 raw23451step0; decide +kernel
      have hl : raw23451step1Labels = raw23451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23451step0 raw23451step0Labels permutation56 hz
    mixedMoment B raw23451step1 raw23451step1Labels = mixedMoment B raw23451step2 raw23451step2Labels := by
      have ha : raw23451step2 = (fun i j => raw23451step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23451step2 raw23451step1; decide +kernel
      have hl : raw23451step2Labels = raw23451step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23451step1 raw23451step1Labels permutation12 permutation3
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw23452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23452step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23452 raw23452Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw23452 raw23452Labels = mixedMoment B raw23452step0 raw23452step0Labels := by
      have hz : ∀ j, raw23452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23452step0 = (fun i j => raw23452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23452step0 raw23452; decide +kernel
      have hl : raw23452step0Labels = raw23452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23452 raw23452Labels permutation346 hz
    mixedMoment B raw23452step0 raw23452step0Labels = mixedMoment B raw23452step1 raw23452step1Labels := by
      have hz : ∀ j, raw23452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23452step1 = (fun i j => raw23452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23452step1 raw23452step0; decide +kernel
      have hl : raw23452step1Labels = raw23452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23452step0 raw23452step0Labels permutation56 hz
    mixedMoment B raw23452step1 raw23452step1Labels = mixedMoment B raw23452step2 raw23452step2Labels := by
      have ha : raw23452step2 = (fun i j => raw23452step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23452step2 raw23452step1; decide +kernel
      have hl : raw23452step2Labels = raw23452step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23452step1 raw23452step1Labels permutation9 permutation3
    _ = mixedMoment B node560 node560Labels := by rfl

def raw23453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23453 raw23453Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23453 raw23453Labels = mixedMoment B raw23453step0 raw23453step0Labels := by
      have hz : ∀ j, raw23453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23453step0 = (fun i j => raw23453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23453step0 raw23453; decide +kernel
      have hl : raw23453step0Labels = raw23453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23453 raw23453Labels permutation346 hz
    mixedMoment B raw23453step0 raw23453step0Labels = mixedMoment B raw23453step1 raw23453step1Labels := by
      have ha : raw23453step1 = (fun i j => raw23453step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23453step1 raw23453step0; decide +kernel
      have hl : raw23453step1Labels = raw23453step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23453step0 raw23453step0Labels permutation33 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw23454step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23454 raw23454Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw23454 raw23454Labels = mixedMoment B raw23454step0 raw23454step0Labels := by
      have hz : ∀ j, raw23454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23454step0 = (fun i j => raw23454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23454step0 raw23454; decide +kernel
      have hl : raw23454step0Labels = raw23454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23454 raw23454Labels permutation265 hz
    mixedMoment B raw23454step0 raw23454step0Labels = mixedMoment B raw23454step1 raw23454step1Labels := by
      have ha : raw23454step1 = (fun i j => raw23454step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23454step1 raw23454step0; decide +kernel
      have hl : raw23454step1Labels = raw23454step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23454step0 raw23454step0Labels permutation33 permutation3
    _ = mixedMoment B node888 node888Labels := by rfl

def raw23455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23455step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw23455step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw23455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23455 raw23455Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw23455 raw23455Labels = mixedMoment B raw23455step0 raw23455step0Labels := by
      have hz : ∀ j, raw23455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23455step0 = (fun i j => raw23455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23455step0 raw23455; decide +kernel
      have hl : raw23455step0Labels = raw23455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23455 raw23455Labels permutation346 hz
    mixedMoment B raw23455step0 raw23455step0Labels = mixedMoment B raw23455step1 raw23455step1Labels := by
      have hz : ∀ j, raw23455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23455step1 = (fun i j => raw23455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23455step1 raw23455step0; decide +kernel
      have hl : raw23455step1Labels = raw23455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23455step0 raw23455step0Labels permutation56 hz
    mixedMoment B raw23455step1 raw23455step1Labels = mixedMoment B raw23455step2 raw23455step2Labels := by
      have ha : raw23455step2 = (fun i j => raw23455step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23455step2 raw23455step1; decide +kernel
      have hl : raw23455step2Labels = raw23455step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23455step1 raw23455step1Labels permutation12 permutation3
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw23456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23456step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23456step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23456step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 4, 1], ![3, -4, 1], ![2, 0, -2]]
def raw23456step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23456step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw23456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23456 raw23456Labels = mixedMoment B node565 node565Labels := by
  calc
    mixedMoment B raw23456 raw23456Labels = mixedMoment B raw23456step0 raw23456step0Labels := by
      have hz : ∀ j, raw23456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23456step0 = (fun i j => raw23456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23456step0 raw23456; decide +kernel
      have hl : raw23456step0Labels = raw23456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23456 raw23456Labels permutation434 hz
    mixedMoment B raw23456step0 raw23456step0Labels = mixedMoment B raw23456step1 raw23456step1Labels := by
      have hz : ∀ j, raw23456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23456step1 = (fun i j => raw23456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23456step1 raw23456step0; decide +kernel
      have hl : raw23456step1Labels = raw23456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23456step0 raw23456step0Labels permutation80 hz
    mixedMoment B raw23456step1 raw23456step1Labels = mixedMoment B raw23456step2 raw23456step2Labels := by
      have hz : ∀ j, raw23456step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23456step2 = (fun i j => raw23456step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23456step2 raw23456step1; decide +kernel
      have hl : raw23456step2Labels = raw23456step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23456step1 raw23456step1Labels permutation14 hz
    mixedMoment B raw23456step2 raw23456step2Labels = mixedMoment B raw23456step3 raw23456step3Labels := by
      have ha : raw23456step3 = (fun i j => raw23456step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23456step3 raw23456step2; decide +kernel
      have hl : raw23456step3Labels = raw23456step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23456step2 raw23456step2Labels permutation3 permutation3
    _ = mixedMoment B node565 node565Labels := by rfl

def raw23457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23457step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23457 raw23457Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw23457 raw23457Labels = mixedMoment B raw23457step0 raw23457step0Labels := by
      have hz : ∀ j, raw23457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23457step0 = (fun i j => raw23457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23457step0 raw23457; decide +kernel
      have hl : raw23457step0Labels = raw23457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23457 raw23457Labels permutation434 hz
    mixedMoment B raw23457step0 raw23457step0Labels = mixedMoment B raw23457step1 raw23457step1Labels := by
      have hz : ∀ j, raw23457step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23457step1 = (fun i j => raw23457step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23457step1 raw23457step0; decide +kernel
      have hl : raw23457step1Labels = raw23457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23457step0 raw23457step0Labels permutation80 hz
    mixedMoment B raw23457step1 raw23457step1Labels = mixedMoment B raw23457step2 raw23457step2Labels := by
      have ha : raw23457step2 = (fun i j => raw23457step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23457step2 raw23457step1; decide +kernel
      have hl : raw23457step2Labels = raw23457step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23457step1 raw23457step1Labels permutation9 permutation3
    _ = mixedMoment B node894 node894Labels := by rfl

def raw23458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23458step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23458 raw23458Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw23458 raw23458Labels = mixedMoment B raw23458step0 raw23458step0Labels := by
      have hz : ∀ j, raw23458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23458step0 = (fun i j => raw23458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23458step0 raw23458; decide +kernel
      have hl : raw23458step0Labels = raw23458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23458 raw23458Labels permutation434 hz
    mixedMoment B raw23458step0 raw23458step0Labels = mixedMoment B raw23458step1 raw23458step1Labels := by
      have hz : ∀ j, raw23458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23458step1 = (fun i j => raw23458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23458step1 raw23458step0; decide +kernel
      have hl : raw23458step1Labels = raw23458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23458step0 raw23458step0Labels permutation56 hz
    mixedMoment B raw23458step1 raw23458step1Labels = mixedMoment B raw23458step2 raw23458step2Labels := by
      have ha : raw23458step2 = (fun i j => raw23458step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23458step2 raw23458step1; decide +kernel
      have hl : raw23458step2Labels = raw23458step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23458step1 raw23458step1Labels permutation9 permutation3
    _ = mixedMoment B node894 node894Labels := by rfl

def raw23459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23459step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw23459step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw23459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23459 raw23459Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw23459 raw23459Labels = mixedMoment B raw23459step0 raw23459step0Labels := by
      have hz : ∀ j, raw23459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23459step0 = (fun i j => raw23459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23459step0 raw23459; decide +kernel
      have hl : raw23459step0Labels = raw23459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23459 raw23459Labels permutation346 hz
    mixedMoment B raw23459step0 raw23459step0Labels = mixedMoment B raw23459step1 raw23459step1Labels := by
      have hz : ∀ j, raw23459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23459step1 = (fun i j => raw23459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23459step1 raw23459step0; decide +kernel
      have hl : raw23459step1Labels = raw23459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23459step0 raw23459step0Labels permutation56 hz
    mixedMoment B raw23459step1 raw23459step1Labels = mixedMoment B raw23459step2 raw23459step2Labels := by
      have ha : raw23459step2 = (fun i j => raw23459step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23459step2 raw23459step1; decide +kernel
      have hl : raw23459step2Labels = raw23459step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23459step1 raw23459step1Labels permutation9 permutation3
    _ = mixedMoment B node894 node894Labels := by rfl

def raw23460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23460step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw23460step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![3, -4, 1], ![1, 1, -2]]
def raw23460step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23460step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw23460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23460 raw23460Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw23460 raw23460Labels = mixedMoment B raw23460step0 raw23460step0Labels := by
      have hz : ∀ j, raw23460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23460step0 = (fun i j => raw23460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23460step0 raw23460; decide +kernel
      have hl : raw23460step0Labels = raw23460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23460 raw23460Labels permutation434 hz
    mixedMoment B raw23460step0 raw23460step0Labels = mixedMoment B raw23460step1 raw23460step1Labels := by
      have hz : ∀ j, raw23460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23460step1 = (fun i j => raw23460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23460step1 raw23460step0; decide +kernel
      have hl : raw23460step1Labels = raw23460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23460step0 raw23460step0Labels permutation80 hz
    mixedMoment B raw23460step1 raw23460step1Labels = mixedMoment B raw23460step2 raw23460step2Labels := by
      have hz : ∀ j, raw23460step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23460step2 = (fun i j => raw23460step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23460step2 raw23460step1; decide +kernel
      have hl : raw23460step2Labels = raw23460step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23460step1 raw23460step1Labels permutation14 hz
    mixedMoment B raw23460step2 raw23460step2Labels = mixedMoment B raw23460step3 raw23460step3Labels := by
      have ha : raw23460step3 = (fun i j => raw23460step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23460step3 raw23460step2; decide +kernel
      have hl : raw23460step3Labels = raw23460step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23460step2 raw23460step2Labels permutation3 permutation3
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw23461 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23461step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23461step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23461 raw23461Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw23461 raw23461Labels = mixedMoment B raw23461step0 raw23461step0Labels := by
      have hz : ∀ j, raw23461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23461step0 = (fun i j => raw23461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23461step0 raw23461; decide +kernel
      have hl : raw23461step0Labels = raw23461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23461 raw23461Labels permutation434 hz
    mixedMoment B raw23461step0 raw23461step0Labels = mixedMoment B raw23461step1 raw23461step1Labels := by
      have hz : ∀ j, raw23461step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23461step1 = (fun i j => raw23461step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23461step1 raw23461step0; decide +kernel
      have hl : raw23461step1Labels = raw23461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23461step0 raw23461step0Labels permutation80 hz
    mixedMoment B raw23461step1 raw23461step1Labels = mixedMoment B raw23461step2 raw23461step2Labels := by
      have ha : raw23461step2 = (fun i j => raw23461step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23461step2 raw23461step1; decide +kernel
      have hl : raw23461step2Labels = raw23461step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23461step1 raw23461step1Labels permutation9 permutation6
    mixedMoment B raw23461step2 raw23461step2Labels = mixedMoment B raw23461step3 raw23461step3Labels := by
      have ha : raw23461step3 = raw23461step2 := by apply Matrix.ext; unfold raw23461step3 raw23461step2; decide +kernel
      have hl : raw23461step2Labels = labelEmbedding9 ∘ raw23461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23461step2 raw23461step2Labels raw23461step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw23462 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23462step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23462step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23462 raw23462Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw23462 raw23462Labels = mixedMoment B raw23462step0 raw23462step0Labels := by
      have hz : ∀ j, raw23462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23462step0 = (fun i j => raw23462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23462step0 raw23462; decide +kernel
      have hl : raw23462step0Labels = raw23462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23462 raw23462Labels permutation434 hz
    mixedMoment B raw23462step0 raw23462step0Labels = mixedMoment B raw23462step1 raw23462step1Labels := by
      have hz : ∀ j, raw23462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23462step1 = (fun i j => raw23462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23462step1 raw23462step0; decide +kernel
      have hl : raw23462step1Labels = raw23462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23462step0 raw23462step0Labels permutation56 hz
    mixedMoment B raw23462step1 raw23462step1Labels = mixedMoment B raw23462step2 raw23462step2Labels := by
      have ha : raw23462step2 = (fun i j => raw23462step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23462step2 raw23462step1; decide +kernel
      have hl : raw23462step2Labels = raw23462step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23462step1 raw23462step1Labels permutation9 permutation6
    mixedMoment B raw23462step2 raw23462step2Labels = mixedMoment B raw23462step3 raw23462step3Labels := by
      have ha : raw23462step3 = raw23462step2 := by apply Matrix.ext; unfold raw23462step3 raw23462step2; decide +kernel
      have hl : raw23462step2Labels = labelEmbedding9 ∘ raw23462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23462step2 raw23462step2Labels raw23462step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw23463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23463step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-3, 1, 2]]
def raw23463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23463step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw23463step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23463step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw23463step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23463 raw23463Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw23463 raw23463Labels = mixedMoment B raw23463step0 raw23463step0Labels := by
      have hz : ∀ j, raw23463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23463step0 = (fun i j => raw23463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23463step0 raw23463; decide +kernel
      have hl : raw23463step0Labels = raw23463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23463 raw23463Labels permutation434 hz
    mixedMoment B raw23463step0 raw23463step0Labels = mixedMoment B raw23463step1 raw23463step1Labels := by
      have hz : ∀ j, raw23463step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23463step1 = (fun i j => raw23463step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23463step1 raw23463step0; decide +kernel
      have hl : raw23463step1Labels = raw23463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23463step0 raw23463step0Labels permutation80 hz
    mixedMoment B raw23463step1 raw23463step1Labels = mixedMoment B raw23463step2 raw23463step2Labels := by
      have hz : ∀ j, raw23463step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23463step2 = (fun i j => raw23463step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23463step2 raw23463step1; decide +kernel
      have hl : raw23463step2Labels = raw23463step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23463step1 raw23463step1Labels permutation14 hz
    mixedMoment B raw23463step2 raw23463step2Labels = mixedMoment B raw23463step3 raw23463step3Labels := by
      have ha : raw23463step3 = (fun i j => raw23463step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23463step3 raw23463step2; decide +kernel
      have hl : raw23463step3Labels = raw23463step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23463step2 raw23463step2Labels permutation3 permutation6
    mixedMoment B raw23463step3 raw23463step3Labels = mixedMoment B raw23463step4 raw23463step4Labels := by
      have ha : raw23463step4 = raw23463step3 := by apply Matrix.ext; unfold raw23463step4 raw23463step3; decide +kernel
      have hl : raw23463step3Labels = labelEmbedding9 ∘ raw23463step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23463step3 raw23463step3Labels raw23463step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4626 node4626Labels := by rfl

def raw23464 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23464step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23464step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23464step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23464step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23464 raw23464Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw23464 raw23464Labels = mixedMoment B raw23464step0 raw23464step0Labels := by
      have hz : ∀ j, raw23464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23464step0 = (fun i j => raw23464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23464step0 raw23464; decide +kernel
      have hl : raw23464step0Labels = raw23464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23464 raw23464Labels permutation434 hz
    mixedMoment B raw23464step0 raw23464step0Labels = mixedMoment B raw23464step1 raw23464step1Labels := by
      have hz : ∀ j, raw23464step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23464step1 = (fun i j => raw23464step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23464step1 raw23464step0; decide +kernel
      have hl : raw23464step1Labels = raw23464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23464step0 raw23464step0Labels permutation56 hz
    mixedMoment B raw23464step1 raw23464step1Labels = mixedMoment B raw23464step2 raw23464step2Labels := by
      have ha : raw23464step2 = (fun i j => raw23464step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23464step2 raw23464step1; decide +kernel
      have hl : raw23464step2Labels = raw23464step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23464step1 raw23464step1Labels permutation9 permutation6
    mixedMoment B raw23464step2 raw23464step2Labels = mixedMoment B raw23464step3 raw23464step3Labels := by
      have ha : raw23464step3 = raw23464step2 := by apply Matrix.ext; unfold raw23464step3 raw23464step2; decide +kernel
      have hl : raw23464step2Labels = labelEmbedding9 ∘ raw23464step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23464step2 raw23464step2Labels raw23464step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw23465 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23465step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23465 raw23465Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23465 raw23465Labels = mixedMoment B raw23465step0 raw23465step0Labels := by
      have hz : ∀ j, raw23465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23465step0 = (fun i j => raw23465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23465step0 raw23465; decide +kernel
      have hl : raw23465step0Labels = raw23465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23465 raw23465Labels permutation434 hz
    mixedMoment B raw23465step0 raw23465step0Labels = mixedMoment B raw23465step1 raw23465step1Labels := by
      have ha : raw23465step1 = (fun i j => raw23465step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23465step1 raw23465step0; decide +kernel
      have hl : raw23465step1Labels = raw23465step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23465step0 raw23465step0Labels permutation33 permutation6
    mixedMoment B raw23465step1 raw23465step1Labels = mixedMoment B raw23465step2 raw23465step2Labels := by
      have ha : raw23465step2 = raw23465step1 := by apply Matrix.ext; unfold raw23465step2 raw23465step1; decide +kernel
      have hl : raw23465step1Labels = labelEmbedding9 ∘ raw23465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23465step1 raw23465step1Labels raw23465step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23466 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23466step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23466 raw23466Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23466 raw23466Labels = mixedMoment B raw23466step0 raw23466step0Labels := by
      have hz : ∀ j, raw23466 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23466step0 = (fun i j => raw23466 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23466step0 raw23466; decide +kernel
      have hl : raw23466step0Labels = raw23466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23466 raw23466Labels permutation265 hz
    mixedMoment B raw23466step0 raw23466step0Labels = mixedMoment B raw23466step1 raw23466step1Labels := by
      have ha : raw23466step1 = (fun i j => raw23466step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23466step1 raw23466step0; decide +kernel
      have hl : raw23466step1Labels = raw23466step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23466step0 raw23466step0Labels permutation39 permutation6
    mixedMoment B raw23466step1 raw23466step1Labels = mixedMoment B raw23466step2 raw23466step2Labels := by
      have ha : raw23466step2 = raw23466step1 := by apply Matrix.ext; unfold raw23466step2 raw23466step1; decide +kernel
      have hl : raw23466step1Labels = labelEmbedding9 ∘ raw23466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23466step1 raw23466step1Labels raw23466step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23467 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23467step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23467 raw23467Labels = mixedMoment B node4465 node4465Labels := by
  calc
    mixedMoment B raw23467 raw23467Labels = mixedMoment B raw23467step0 raw23467step0Labels := by
      have hz : ∀ j, raw23467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23467step0 = (fun i j => raw23467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23467step0 raw23467; decide +kernel
      have hl : raw23467step0Labels = raw23467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23467 raw23467Labels permutation434 hz
    mixedMoment B raw23467step0 raw23467step0Labels = mixedMoment B raw23467step1 raw23467step1Labels := by
      have hz : ∀ j, raw23467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23467step1 = (fun i j => raw23467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23467step1 raw23467step0; decide +kernel
      have hl : raw23467step1Labels = raw23467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23467step0 raw23467step0Labels permutation56 hz
    mixedMoment B raw23467step1 raw23467step1Labels = mixedMoment B raw23467step2 raw23467step2Labels := by
      have ha : raw23467step2 = (fun i j => raw23467step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23467step2 raw23467step1; decide +kernel
      have hl : raw23467step2Labels = raw23467step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23467step1 raw23467step1Labels permutation9 permutation6
    mixedMoment B raw23467step2 raw23467step2Labels = mixedMoment B raw23467step3 raw23467step3Labels := by
      have ha : raw23467step3 = raw23467step2 := by apply Matrix.ext; unfold raw23467step3 raw23467step2; decide +kernel
      have hl : raw23467step2Labels = labelEmbedding9 ∘ raw23467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23467step2 raw23467step2Labels raw23467step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4465 node4465Labels := by rfl

def raw23468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23468step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23468 raw23468Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw23468 raw23468Labels = mixedMoment B raw23468step0 raw23468step0Labels := by
      have hz : ∀ j, raw23468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23468step0 = (fun i j => raw23468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23468step0 raw23468; decide +kernel
      have hl : raw23468step0Labels = raw23468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23468 raw23468Labels permutation346 hz
    mixedMoment B raw23468step0 raw23468step0Labels = mixedMoment B raw23468step1 raw23468step1Labels := by
      have hz : ∀ j, raw23468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23468step1 = (fun i j => raw23468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23468step1 raw23468step0; decide +kernel
      have hl : raw23468step1Labels = raw23468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23468step0 raw23468step0Labels permutation56 hz
    mixedMoment B raw23468step1 raw23468step1Labels = mixedMoment B raw23468step2 raw23468step2Labels := by
      have ha : raw23468step2 = (fun i j => raw23468step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23468step2 raw23468step1; decide +kernel
      have hl : raw23468step2Labels = raw23468step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23468step1 raw23468step1Labels permutation9 permutation6
    mixedMoment B raw23468step2 raw23468step2Labels = mixedMoment B raw23468step3 raw23468step3Labels := by
      have ha : raw23468step3 = raw23468step2 := by apply Matrix.ext; unfold raw23468step3 raw23468step2; decide +kernel
      have hl : raw23468step2Labels = labelEmbedding9 ∘ raw23468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23468step2 raw23468step2Labels raw23468step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw23469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23469step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23469 raw23469Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23469 raw23469Labels = mixedMoment B raw23469step0 raw23469step0Labels := by
      have hz : ∀ j, raw23469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23469step0 = (fun i j => raw23469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23469step0 raw23469; decide +kernel
      have hl : raw23469step0Labels = raw23469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23469 raw23469Labels permutation346 hz
    mixedMoment B raw23469step0 raw23469step0Labels = mixedMoment B raw23469step1 raw23469step1Labels := by
      have ha : raw23469step1 = (fun i j => raw23469step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23469step1 raw23469step0; decide +kernel
      have hl : raw23469step1Labels = raw23469step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23469step0 raw23469step0Labels permutation33 permutation6
    mixedMoment B raw23469step1 raw23469step1Labels = mixedMoment B raw23469step2 raw23469step2Labels := by
      have ha : raw23469step2 = raw23469step1 := by apply Matrix.ext; unfold raw23469step2 raw23469step1; decide +kernel
      have hl : raw23469step1Labels = labelEmbedding9 ∘ raw23469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23469step1 raw23469step1Labels raw23469step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23470 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23470step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23470 raw23470Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23470 raw23470Labels = mixedMoment B raw23470step0 raw23470step0Labels := by
      have hz : ∀ j, raw23470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23470step0 = (fun i j => raw23470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23470step0 raw23470; decide +kernel
      have hl : raw23470step0Labels = raw23470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23470 raw23470Labels permutation265 hz
    mixedMoment B raw23470step0 raw23470step0Labels = mixedMoment B raw23470step1 raw23470step1Labels := by
      have ha : raw23470step1 = (fun i j => raw23470step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23470step1 raw23470step0; decide +kernel
      have hl : raw23470step1Labels = raw23470step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23470step0 raw23470step0Labels permutation33 permutation6
    mixedMoment B raw23470step1 raw23470step1Labels = mixedMoment B raw23470step2 raw23470step2Labels := by
      have ha : raw23470step2 = raw23470step1 := by apply Matrix.ext; unfold raw23470step2 raw23470step1; decide +kernel
      have hl : raw23470step1Labels = labelEmbedding9 ∘ raw23470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23470step1 raw23470step1Labels raw23470step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23471 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23471step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23471 raw23471Labels = mixedMoment B node4465 node4465Labels := by
  calc
    mixedMoment B raw23471 raw23471Labels = mixedMoment B raw23471step0 raw23471step0Labels := by
      have hz : ∀ j, raw23471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23471step0 = (fun i j => raw23471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23471step0 raw23471; decide +kernel
      have hl : raw23471step0Labels = raw23471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23471 raw23471Labels permutation346 hz
    mixedMoment B raw23471step0 raw23471step0Labels = mixedMoment B raw23471step1 raw23471step1Labels := by
      have hz : ∀ j, raw23471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23471step1 = (fun i j => raw23471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23471step1 raw23471step0; decide +kernel
      have hl : raw23471step1Labels = raw23471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23471step0 raw23471step0Labels permutation56 hz
    mixedMoment B raw23471step1 raw23471step1Labels = mixedMoment B raw23471step2 raw23471step2Labels := by
      have ha : raw23471step2 = (fun i j => raw23471step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23471step2 raw23471step1; decide +kernel
      have hl : raw23471step2Labels = raw23471step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23471step1 raw23471step1Labels permutation9 permutation6
    mixedMoment B raw23471step2 raw23471step2Labels = mixedMoment B raw23471step3 raw23471step3Labels := by
      have ha : raw23471step3 = raw23471step2 := by apply Matrix.ext; unfold raw23471step3 raw23471step2; decide +kernel
      have hl : raw23471step2Labels = labelEmbedding9 ∘ raw23471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23471step2 raw23471step2Labels raw23471step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4465 node4465Labels := by rfl

def raw23472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23472step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -4, 2], ![-2, 0, 2]]
def raw23472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23472step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-4, 2, 2]]
def raw23472step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23472step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw23472step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23472step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw23472step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23472 raw23472Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw23472 raw23472Labels = mixedMoment B raw23472step0 raw23472step0Labels := by
      have hz : ∀ j, raw23472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23472step0 = (fun i j => raw23472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23472step0 raw23472; decide +kernel
      have hl : raw23472step0Labels = raw23472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23472 raw23472Labels permutation434 hz
    mixedMoment B raw23472step0 raw23472step0Labels = mixedMoment B raw23472step1 raw23472step1Labels := by
      have hz : ∀ j, raw23472step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23472step1 = (fun i j => raw23472step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23472step1 raw23472step0; decide +kernel
      have hl : raw23472step1Labels = raw23472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23472step0 raw23472step0Labels permutation80 hz
    mixedMoment B raw23472step1 raw23472step1Labels = mixedMoment B raw23472step2 raw23472step2Labels := by
      have hz : ∀ j, raw23472step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23472step2 = (fun i j => raw23472step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23472step2 raw23472step1; decide +kernel
      have hl : raw23472step2Labels = raw23472step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23472step1 raw23472step1Labels permutation14 hz
    mixedMoment B raw23472step2 raw23472step2Labels = mixedMoment B raw23472step3 raw23472step3Labels := by
      have ha : raw23472step3 = (fun i j => raw23472step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23472step3 raw23472step2; decide +kernel
      have hl : raw23472step3Labels = raw23472step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23472step2 raw23472step2Labels permutation3 permutation4
    mixedMoment B raw23472step3 raw23472step3Labels = mixedMoment B raw23472step4 raw23472step4Labels := by
      have ha : raw23472step4 = -raw23472step3 := by apply Matrix.ext; change ∀ i j, raw23472step4 i j = -(raw23472step3 i j); unfold raw23472step4 raw23472step3; decide +kernel
      have hl : raw23472step4Labels = raw23472step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23472step4 raw23472step4Labels = mixedMoment B raw23472step5 raw23472step5Labels := by
      have ha : raw23472step5 = raw23472step4 := by apply Matrix.ext; unfold raw23472step5 raw23472step4; decide +kernel
      have hl : raw23472step4Labels = labelEmbedding7 ∘ raw23472step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23472step4 raw23472step4Labels raw23472step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

def raw23473 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23473step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23473step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23473step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23473 raw23473Labels = mixedMoment B node4430 node4430Labels := by
  calc
    mixedMoment B raw23473 raw23473Labels = mixedMoment B raw23473step0 raw23473step0Labels := by
      have hz : ∀ j, raw23473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23473step0 = (fun i j => raw23473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23473step0 raw23473; decide +kernel
      have hl : raw23473step0Labels = raw23473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23473 raw23473Labels permutation434 hz
    mixedMoment B raw23473step0 raw23473step0Labels = mixedMoment B raw23473step1 raw23473step1Labels := by
      have hz : ∀ j, raw23473step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23473step1 = (fun i j => raw23473step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23473step1 raw23473step0; decide +kernel
      have hl : raw23473step1Labels = raw23473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23473step0 raw23473step0Labels permutation80 hz
    mixedMoment B raw23473step1 raw23473step1Labels = mixedMoment B raw23473step2 raw23473step2Labels := by
      have ha : raw23473step2 = (fun i j => raw23473step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23473step2 raw23473step1; decide +kernel
      have hl : raw23473step2Labels = raw23473step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23473step1 raw23473step1Labels permutation9 permutation6
    mixedMoment B raw23473step2 raw23473step2Labels = mixedMoment B raw23473step3 raw23473step3Labels := by
      have ha : raw23473step3 = raw23473step2 := by apply Matrix.ext; unfold raw23473step3 raw23473step2; decide +kernel
      have hl : raw23473step2Labels = labelEmbedding9 ∘ raw23473step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23473step2 raw23473step2Labels raw23473step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4430 node4430Labels := by rfl

def raw23474 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23474step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23474 raw23474Labels = mixedMoment B node4430 node4430Labels := by
  calc
    mixedMoment B raw23474 raw23474Labels = mixedMoment B raw23474step0 raw23474step0Labels := by
      have hz : ∀ j, raw23474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23474step0 = (fun i j => raw23474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23474step0 raw23474; decide +kernel
      have hl : raw23474step0Labels = raw23474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23474 raw23474Labels permutation434 hz
    mixedMoment B raw23474step0 raw23474step0Labels = mixedMoment B raw23474step1 raw23474step1Labels := by
      have hz : ∀ j, raw23474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23474step1 = (fun i j => raw23474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23474step1 raw23474step0; decide +kernel
      have hl : raw23474step1Labels = raw23474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23474step0 raw23474step0Labels permutation56 hz
    mixedMoment B raw23474step1 raw23474step1Labels = mixedMoment B raw23474step2 raw23474step2Labels := by
      have ha : raw23474step2 = (fun i j => raw23474step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23474step2 raw23474step1; decide +kernel
      have hl : raw23474step2Labels = raw23474step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23474step1 raw23474step1Labels permutation9 permutation6
    mixedMoment B raw23474step2 raw23474step2Labels = mixedMoment B raw23474step3 raw23474step3Labels := by
      have ha : raw23474step3 = raw23474step2 := by apply Matrix.ext; unfold raw23474step3 raw23474step2; decide +kernel
      have hl : raw23474step2Labels = labelEmbedding9 ∘ raw23474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23474step2 raw23474step2Labels raw23474step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4430 node4430Labels := by rfl

def raw23475 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23475step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23475 raw23475Labels = mixedMoment B node4430 node4430Labels := by
  calc
    mixedMoment B raw23475 raw23475Labels = mixedMoment B raw23475step0 raw23475step0Labels := by
      have hz : ∀ j, raw23475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23475step0 = (fun i j => raw23475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23475step0 raw23475; decide +kernel
      have hl : raw23475step0Labels = raw23475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23475 raw23475Labels permutation346 hz
    mixedMoment B raw23475step0 raw23475step0Labels = mixedMoment B raw23475step1 raw23475step1Labels := by
      have hz : ∀ j, raw23475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23475step1 = (fun i j => raw23475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23475step1 raw23475step0; decide +kernel
      have hl : raw23475step1Labels = raw23475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23475step0 raw23475step0Labels permutation56 hz
    mixedMoment B raw23475step1 raw23475step1Labels = mixedMoment B raw23475step2 raw23475step2Labels := by
      have ha : raw23475step2 = (fun i j => raw23475step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23475step2 raw23475step1; decide +kernel
      have hl : raw23475step2Labels = raw23475step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23475step1 raw23475step1Labels permutation9 permutation6
    mixedMoment B raw23475step2 raw23475step2Labels = mixedMoment B raw23475step3 raw23475step3Labels := by
      have ha : raw23475step3 = raw23475step2 := by apply Matrix.ext; unfold raw23475step3 raw23475step2; decide +kernel
      have hl : raw23475step2Labels = labelEmbedding9 ∘ raw23475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23475step2 raw23475step2Labels raw23475step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4430 node4430Labels := by rfl

def raw23476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -4, 2], ![-3, 1, 2]]
def raw23476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw23476step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23476step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw23476step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23476 raw23476Labels = mixedMoment B node4509 node4509Labels := by
  calc
    mixedMoment B raw23476 raw23476Labels = mixedMoment B raw23476step0 raw23476step0Labels := by
      have hz : ∀ j, raw23476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23476step0 = (fun i j => raw23476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23476step0 raw23476; decide +kernel
      have hl : raw23476step0Labels = raw23476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23476 raw23476Labels permutation434 hz
    mixedMoment B raw23476step0 raw23476step0Labels = mixedMoment B raw23476step1 raw23476step1Labels := by
      have hz : ∀ j, raw23476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23476step1 = (fun i j => raw23476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23476step1 raw23476step0; decide +kernel
      have hl : raw23476step1Labels = raw23476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23476step0 raw23476step0Labels permutation80 hz
    mixedMoment B raw23476step1 raw23476step1Labels = mixedMoment B raw23476step2 raw23476step2Labels := by
      have hz : ∀ j, raw23476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23476step2 = (fun i j => raw23476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23476step2 raw23476step1; decide +kernel
      have hl : raw23476step2Labels = raw23476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23476step1 raw23476step1Labels permutation14 hz
    mixedMoment B raw23476step2 raw23476step2Labels = mixedMoment B raw23476step3 raw23476step3Labels := by
      have ha : raw23476step3 = (fun i j => raw23476step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23476step3 raw23476step2; decide +kernel
      have hl : raw23476step3Labels = raw23476step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23476step2 raw23476step2Labels permutation3 permutation6
    mixedMoment B raw23476step3 raw23476step3Labels = mixedMoment B raw23476step4 raw23476step4Labels := by
      have ha : raw23476step4 = raw23476step3 := by apply Matrix.ext; unfold raw23476step4 raw23476step3; decide +kernel
      have hl : raw23476step3Labels = labelEmbedding9 ∘ raw23476step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23476step3 raw23476step3Labels raw23476step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4509 node4509Labels := by rfl

def raw23477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -3, 2], ![-1, -1, 2]]
def raw23477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-3, 1, 2]]
def raw23477step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23477step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw23477step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23477 raw23477Labels = mixedMoment B node4284 node4284Labels := by
  calc
    mixedMoment B raw23477 raw23477Labels = mixedMoment B raw23477step0 raw23477step0Labels := by
      have hz : ∀ j, raw23477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23477step0 = (fun i j => raw23477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23477step0 raw23477; decide +kernel
      have hl : raw23477step0Labels = raw23477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477 raw23477Labels permutation434 hz
    mixedMoment B raw23477step0 raw23477step0Labels = mixedMoment B raw23477step1 raw23477step1Labels := by
      have hz : ∀ j, raw23477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23477step1 = (fun i j => raw23477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23477step1 raw23477step0; decide +kernel
      have hl : raw23477step1Labels = raw23477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477step0 raw23477step0Labels permutation80 hz
    mixedMoment B raw23477step1 raw23477step1Labels = mixedMoment B raw23477step2 raw23477step2Labels := by
      have hz : ∀ j, raw23477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23477step2 = (fun i j => raw23477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23477step2 raw23477step1; decide +kernel
      have hl : raw23477step2Labels = raw23477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23477step1 raw23477step1Labels permutation14 hz
    mixedMoment B raw23477step2 raw23477step2Labels = mixedMoment B raw23477step3 raw23477step3Labels := by
      have ha : raw23477step3 = (fun i j => raw23477step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23477step3 raw23477step2; decide +kernel
      have hl : raw23477step3Labels = raw23477step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23477step2 raw23477step2Labels permutation3 permutation4
    mixedMoment B raw23477step3 raw23477step3Labels = mixedMoment B raw23477step4 raw23477step4Labels := by
      have ha : raw23477step4 = -raw23477step3 := by apply Matrix.ext; change ∀ i j, raw23477step4 i j = -(raw23477step3 i j); unfold raw23477step4 raw23477step3; decide +kernel
      have hl : raw23477step4Labels = raw23477step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23477step4 raw23477step4Labels = mixedMoment B raw23477step5 raw23477step5Labels := by
      have ha : raw23477step5 = raw23477step4 := by apply Matrix.ext; unfold raw23477step5 raw23477step4; decide +kernel
      have hl : raw23477step4Labels = labelEmbedding7 ∘ raw23477step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23477step4 raw23477step4Labels raw23477step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4284 node4284Labels := by rfl

def raw23478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23478 raw23478Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw23478 raw23478Labels = mixedMoment B raw23478step0 raw23478step0Labels := by
      have hz : ∀ j, raw23478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23478step0 = (fun i j => raw23478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23478step0 raw23478; decide +kernel
      have hl : raw23478step0Labels = raw23478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23478 raw23478Labels permutation434 hz
    mixedMoment B raw23478step0 raw23478step0Labels = mixedMoment B raw23478step1 raw23478step1Labels := by
      have hz : ∀ j, raw23478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23478step1 = (fun i j => raw23478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23478step1 raw23478step0; decide +kernel
      have hl : raw23478step1Labels = raw23478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23478step0 raw23478step0Labels permutation80 hz
    mixedMoment B raw23478step1 raw23478step1Labels = mixedMoment B raw23478step2 raw23478step2Labels := by
      have ha : raw23478step2 = (fun i j => raw23478step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23478step2 raw23478step1; decide +kernel
      have hl : raw23478step2Labels = raw23478step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23478step1 raw23478step1Labels permutation9 permutation6
    mixedMoment B raw23478step2 raw23478step2Labels = mixedMoment B raw23478step3 raw23478step3Labels := by
      have ha : raw23478step3 = raw23478step2 := by apply Matrix.ext; unfold raw23478step3 raw23478step2; decide +kernel
      have hl : raw23478step2Labels = labelEmbedding9 ∘ raw23478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23478step2 raw23478step2Labels raw23478step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw23479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23479 raw23479Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw23479 raw23479Labels = mixedMoment B raw23479step0 raw23479step0Labels := by
      have hz : ∀ j, raw23479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23479step0 = (fun i j => raw23479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23479step0 raw23479; decide +kernel
      have hl : raw23479step0Labels = raw23479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23479 raw23479Labels permutation434 hz
    mixedMoment B raw23479step0 raw23479step0Labels = mixedMoment B raw23479step1 raw23479step1Labels := by
      have hz : ∀ j, raw23479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23479step1 = (fun i j => raw23479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23479step1 raw23479step0; decide +kernel
      have hl : raw23479step1Labels = raw23479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23479step0 raw23479step0Labels permutation56 hz
    mixedMoment B raw23479step1 raw23479step1Labels = mixedMoment B raw23479step2 raw23479step2Labels := by
      have ha : raw23479step2 = (fun i j => raw23479step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23479step2 raw23479step1; decide +kernel
      have hl : raw23479step2Labels = raw23479step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23479step1 raw23479step1Labels permutation9 permutation6
    mixedMoment B raw23479step2 raw23479step2Labels = mixedMoment B raw23479step3 raw23479step3Labels := by
      have ha : raw23479step3 = raw23479step2 := by apply Matrix.ext; unfold raw23479step3 raw23479step2; decide +kernel
      have hl : raw23479step2Labels = labelEmbedding9 ∘ raw23479step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23479step2 raw23479step2Labels raw23479step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw23480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23480 raw23480Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw23480 raw23480Labels = mixedMoment B raw23480step0 raw23480step0Labels := by
      have hz : ∀ j, raw23480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23480step0 = (fun i j => raw23480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23480step0 raw23480; decide +kernel
      have hl : raw23480step0Labels = raw23480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23480 raw23480Labels permutation434 hz
    mixedMoment B raw23480step0 raw23480step0Labels = mixedMoment B raw23480step1 raw23480step1Labels := by
      have hz : ∀ j, raw23480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23480step1 = (fun i j => raw23480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23480step1 raw23480step0; decide +kernel
      have hl : raw23480step1Labels = raw23480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23480step0 raw23480step0Labels permutation80 hz
    mixedMoment B raw23480step1 raw23480step1Labels = mixedMoment B raw23480step2 raw23480step2Labels := by
      have ha : raw23480step2 = (fun i j => raw23480step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23480step2 raw23480step1; decide +kernel
      have hl : raw23480step2Labels = raw23480step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23480step1 raw23480step1Labels permutation9 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw23481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23481 raw23481Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw23481 raw23481Labels = mixedMoment B raw23481step0 raw23481step0Labels := by
      have hz : ∀ j, raw23481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23481step0 = (fun i j => raw23481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23481step0 raw23481; decide +kernel
      have hl : raw23481step0Labels = raw23481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23481 raw23481Labels permutation434 hz
    mixedMoment B raw23481step0 raw23481step0Labels = mixedMoment B raw23481step1 raw23481step1Labels := by
      have hz : ∀ j, raw23481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23481step1 = (fun i j => raw23481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23481step1 raw23481step0; decide +kernel
      have hl : raw23481step1Labels = raw23481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23481step0 raw23481step0Labels permutation56 hz
    mixedMoment B raw23481step1 raw23481step1Labels = mixedMoment B raw23481step2 raw23481step2Labels := by
      have ha : raw23481step2 = (fun i j => raw23481step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23481step2 raw23481step1; decide +kernel
      have hl : raw23481step2Labels = raw23481step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23481step1 raw23481step1Labels permutation9 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw23482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23482step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-3, 1, 2]]
def raw23482step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23482step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw23482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23482 raw23482Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw23482 raw23482Labels = mixedMoment B raw23482step0 raw23482step0Labels := by
      have hz : ∀ j, raw23482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23482step0 = (fun i j => raw23482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23482step0 raw23482; decide +kernel
      have hl : raw23482step0Labels = raw23482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23482 raw23482Labels permutation434 hz
    mixedMoment B raw23482step0 raw23482step0Labels = mixedMoment B raw23482step1 raw23482step1Labels := by
      have hz : ∀ j, raw23482step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23482step1 = (fun i j => raw23482step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23482step1 raw23482step0; decide +kernel
      have hl : raw23482step1Labels = raw23482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23482step0 raw23482step0Labels permutation80 hz
    mixedMoment B raw23482step1 raw23482step1Labels = mixedMoment B raw23482step2 raw23482step2Labels := by
      have hz : ∀ j, raw23482step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23482step2 = (fun i j => raw23482step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23482step2 raw23482step1; decide +kernel
      have hl : raw23482step2Labels = raw23482step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23482step1 raw23482step1Labels permutation14 hz
    mixedMoment B raw23482step2 raw23482step2Labels = mixedMoment B raw23482step3 raw23482step3Labels := by
      have ha : raw23482step3 = (fun i j => raw23482step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23482step3 raw23482step2; decide +kernel
      have hl : raw23482step3Labels = raw23482step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23482step2 raw23482step2Labels permutation3 permutation6
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw23483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23483 raw23483Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw23483 raw23483Labels = mixedMoment B raw23483step0 raw23483step0Labels := by
      have hz : ∀ j, raw23483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23483step0 = (fun i j => raw23483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23483step0 raw23483; decide +kernel
      have hl : raw23483step0Labels = raw23483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23483 raw23483Labels permutation434 hz
    mixedMoment B raw23483step0 raw23483step0Labels = mixedMoment B raw23483step1 raw23483step1Labels := by
      have hz : ∀ j, raw23483step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23483step1 = (fun i j => raw23483step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23483step1 raw23483step0; decide +kernel
      have hl : raw23483step1Labels = raw23483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23483step0 raw23483step0Labels permutation56 hz
    mixedMoment B raw23483step1 raw23483step1Labels = mixedMoment B raw23483step2 raw23483step2Labels := by
      have ha : raw23483step2 = (fun i j => raw23483step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23483step2 raw23483step1; decide +kernel
      have hl : raw23483step2Labels = raw23483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23483step1 raw23483step1Labels permutation9 permutation6
    _ = mixedMoment B node815 node815Labels := by rfl

def raw23484 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23484 raw23484Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23484 raw23484Labels = mixedMoment B raw23484step0 raw23484step0Labels := by
      have hz : ∀ j, raw23484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23484step0 = (fun i j => raw23484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23484step0 raw23484; decide +kernel
      have hl : raw23484step0Labels = raw23484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23484 raw23484Labels permutation434 hz
    mixedMoment B raw23484step0 raw23484step0Labels = mixedMoment B raw23484step1 raw23484step1Labels := by
      have ha : raw23484step1 = (fun i j => raw23484step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23484step1 raw23484step0; decide +kernel
      have hl : raw23484step1Labels = raw23484step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23484step0 raw23484step0Labels permutation33 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23485 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23485 raw23485Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23485 raw23485Labels = mixedMoment B raw23485step0 raw23485step0Labels := by
      have hz : ∀ j, raw23485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23485step0 = (fun i j => raw23485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23485step0 raw23485; decide +kernel
      have hl : raw23485step0Labels = raw23485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23485 raw23485Labels permutation265 hz
    mixedMoment B raw23485step0 raw23485step0Labels = mixedMoment B raw23485step1 raw23485step1Labels := by
      have ha : raw23485step1 = (fun i j => raw23485step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23485step1 raw23485step0; decide +kernel
      have hl : raw23485step1Labels = raw23485step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23485step0 raw23485step0Labels permutation39 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23486 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23486 raw23486Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw23486 raw23486Labels = mixedMoment B raw23486step0 raw23486step0Labels := by
      have hz : ∀ j, raw23486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23486step0 = (fun i j => raw23486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23486step0 raw23486; decide +kernel
      have hl : raw23486step0Labels = raw23486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23486 raw23486Labels permutation434 hz
    mixedMoment B raw23486step0 raw23486step0Labels = mixedMoment B raw23486step1 raw23486step1Labels := by
      have hz : ∀ j, raw23486step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23486step1 = (fun i j => raw23486step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23486step1 raw23486step0; decide +kernel
      have hl : raw23486step1Labels = raw23486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23486step0 raw23486step0Labels permutation56 hz
    mixedMoment B raw23486step1 raw23486step1Labels = mixedMoment B raw23486step2 raw23486step2Labels := by
      have ha : raw23486step2 = (fun i j => raw23486step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23486step2 raw23486step1; decide +kernel
      have hl : raw23486step2Labels = raw23486step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23486step1 raw23486step1Labels permutation9 permutation6
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw23487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23487 raw23487Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw23487 raw23487Labels = mixedMoment B raw23487step0 raw23487step0Labels := by
      have hz : ∀ j, raw23487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23487step0 = (fun i j => raw23487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23487step0 raw23487; decide +kernel
      have hl : raw23487step0Labels = raw23487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23487 raw23487Labels permutation346 hz
    mixedMoment B raw23487step0 raw23487step0Labels = mixedMoment B raw23487step1 raw23487step1Labels := by
      have hz : ∀ j, raw23487step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23487step1 = (fun i j => raw23487step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23487step1 raw23487step0; decide +kernel
      have hl : raw23487step1Labels = raw23487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23487step0 raw23487step0Labels permutation56 hz
    mixedMoment B raw23487step1 raw23487step1Labels = mixedMoment B raw23487step2 raw23487step2Labels := by
      have ha : raw23487step2 = (fun i j => raw23487step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23487step2 raw23487step1; decide +kernel
      have hl : raw23487step2Labels = raw23487step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23487step1 raw23487step1Labels permutation9 permutation6
    _ = mixedMoment B node815 node815Labels := by rfl

def raw23488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23488 raw23488Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23488 raw23488Labels = mixedMoment B raw23488step0 raw23488step0Labels := by
      have hz : ∀ j, raw23488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23488step0 = (fun i j => raw23488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23488step0 raw23488; decide +kernel
      have hl : raw23488step0Labels = raw23488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23488 raw23488Labels permutation346 hz
    mixedMoment B raw23488step0 raw23488step0Labels = mixedMoment B raw23488step1 raw23488step1Labels := by
      have ha : raw23488step1 = (fun i j => raw23488step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23488step1 raw23488step0; decide +kernel
      have hl : raw23488step1Labels = raw23488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23488step0 raw23488step0Labels permutation33 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23489 raw23489Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23489 raw23489Labels = mixedMoment B raw23489step0 raw23489step0Labels := by
      have hz : ∀ j, raw23489 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23489step0 = (fun i j => raw23489 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23489step0 raw23489; decide +kernel
      have hl : raw23489step0Labels = raw23489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23489 raw23489Labels permutation265 hz
    mixedMoment B raw23489step0 raw23489step0Labels = mixedMoment B raw23489step1 raw23489step1Labels := by
      have ha : raw23489step1 = (fun i j => raw23489step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23489step1 raw23489step0; decide +kernel
      have hl : raw23489step1Labels = raw23489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23489step0 raw23489step0Labels permutation33 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23490 raw23490Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw23490 raw23490Labels = mixedMoment B raw23490step0 raw23490step0Labels := by
      have hz : ∀ j, raw23490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23490step0 = (fun i j => raw23490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23490step0 raw23490; decide +kernel
      have hl : raw23490step0Labels = raw23490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23490 raw23490Labels permutation346 hz
    mixedMoment B raw23490step0 raw23490step0Labels = mixedMoment B raw23490step1 raw23490step1Labels := by
      have hz : ∀ j, raw23490step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23490step1 = (fun i j => raw23490step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23490step1 raw23490step0; decide +kernel
      have hl : raw23490step1Labels = raw23490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23490step0 raw23490step0Labels permutation56 hz
    mixedMoment B raw23490step1 raw23490step1Labels = mixedMoment B raw23490step2 raw23490step2Labels := by
      have ha : raw23490step2 = (fun i j => raw23490step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23490step2 raw23490step1; decide +kernel
      have hl : raw23490step2Labels = raw23490step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23490step1 raw23490step1Labels permutation9 permutation6
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw23491 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23491step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23491step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -4, 2], ![-2, 0, 2]]
def raw23491step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23491step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw23491step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23491 raw23491Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw23491 raw23491Labels = mixedMoment B raw23491step0 raw23491step0Labels := by
      have hz : ∀ j, raw23491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23491step0 = (fun i j => raw23491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23491step0 raw23491; decide +kernel
      have hl : raw23491step0Labels = raw23491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23491 raw23491Labels permutation434 hz
    mixedMoment B raw23491step0 raw23491step0Labels = mixedMoment B raw23491step1 raw23491step1Labels := by
      have hz : ∀ j, raw23491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23491step1 = (fun i j => raw23491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23491step1 raw23491step0; decide +kernel
      have hl : raw23491step1Labels = raw23491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23491step0 raw23491step0Labels permutation80 hz
    mixedMoment B raw23491step1 raw23491step1Labels = mixedMoment B raw23491step2 raw23491step2Labels := by
      have hz : ∀ j, raw23491step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23491step2 = (fun i j => raw23491step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23491step2 raw23491step1; decide +kernel
      have hl : raw23491step2Labels = raw23491step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23491step1 raw23491step1Labels permutation14 hz
    mixedMoment B raw23491step2 raw23491step2Labels = mixedMoment B raw23491step3 raw23491step3Labels := by
      have ha : raw23491step3 = (fun i j => raw23491step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23491step3 raw23491step2; decide +kernel
      have hl : raw23491step3Labels = raw23491step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23491step2 raw23491step2Labels permutation3 permutation6
    _ = mixedMoment B node862 node862Labels := by rfl

def raw23492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23492step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23492 raw23492Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw23492 raw23492Labels = mixedMoment B raw23492step0 raw23492step0Labels := by
      have hz : ∀ j, raw23492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23492step0 = (fun i j => raw23492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23492step0 raw23492; decide +kernel
      have hl : raw23492step0Labels = raw23492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23492 raw23492Labels permutation434 hz
    mixedMoment B raw23492step0 raw23492step0Labels = mixedMoment B raw23492step1 raw23492step1Labels := by
      have hz : ∀ j, raw23492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23492step1 = (fun i j => raw23492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23492step1 raw23492step0; decide +kernel
      have hl : raw23492step1Labels = raw23492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23492step0 raw23492step0Labels permutation80 hz
    mixedMoment B raw23492step1 raw23492step1Labels = mixedMoment B raw23492step2 raw23492step2Labels := by
      have ha : raw23492step2 = (fun i j => raw23492step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23492step2 raw23492step1; decide +kernel
      have hl : raw23492step2Labels = raw23492step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23492step1 raw23492step1Labels permutation9 permutation6
    _ = mixedMoment B node1011 node1011Labels := by rfl

def raw23493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23493 raw23493Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw23493 raw23493Labels = mixedMoment B raw23493step0 raw23493step0Labels := by
      have hz : ∀ j, raw23493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23493step0 = (fun i j => raw23493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23493step0 raw23493; decide +kernel
      have hl : raw23493step0Labels = raw23493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23493 raw23493Labels permutation434 hz
    mixedMoment B raw23493step0 raw23493step0Labels = mixedMoment B raw23493step1 raw23493step1Labels := by
      have hz : ∀ j, raw23493step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23493step1 = (fun i j => raw23493step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23493step1 raw23493step0; decide +kernel
      have hl : raw23493step1Labels = raw23493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23493step0 raw23493step0Labels permutation56 hz
    mixedMoment B raw23493step1 raw23493step1Labels = mixedMoment B raw23493step2 raw23493step2Labels := by
      have ha : raw23493step2 = (fun i j => raw23493step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23493step2 raw23493step1; decide +kernel
      have hl : raw23493step2Labels = raw23493step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23493step1 raw23493step1Labels permutation9 permutation6
    _ = mixedMoment B node1011 node1011Labels := by rfl

def raw23494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23494 raw23494Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw23494 raw23494Labels = mixedMoment B raw23494step0 raw23494step0Labels := by
      have hz : ∀ j, raw23494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23494step0 = (fun i j => raw23494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23494step0 raw23494; decide +kernel
      have hl : raw23494step0Labels = raw23494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23494 raw23494Labels permutation346 hz
    mixedMoment B raw23494step0 raw23494step0Labels = mixedMoment B raw23494step1 raw23494step1Labels := by
      have hz : ∀ j, raw23494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23494step1 = (fun i j => raw23494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23494step1 raw23494step0; decide +kernel
      have hl : raw23494step1Labels = raw23494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23494step0 raw23494step0Labels permutation56 hz
    mixedMoment B raw23494step1 raw23494step1Labels = mixedMoment B raw23494step2 raw23494step2Labels := by
      have ha : raw23494step2 = (fun i j => raw23494step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23494step2 raw23494step1; decide +kernel
      have hl : raw23494step2Labels = raw23494step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23494step1 raw23494step1Labels permutation9 permutation6
    _ = mixedMoment B node1011 node1011Labels := by rfl

def raw23495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23495step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -4, 2], ![-3, 1, 2]]
def raw23495step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23495step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw23495step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23495 raw23495Labels = mixedMoment B node1093 node1093Labels := by
  calc
    mixedMoment B raw23495 raw23495Labels = mixedMoment B raw23495step0 raw23495step0Labels := by
      have hz : ∀ j, raw23495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23495step0 = (fun i j => raw23495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23495step0 raw23495; decide +kernel
      have hl : raw23495step0Labels = raw23495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23495 raw23495Labels permutation434 hz
    mixedMoment B raw23495step0 raw23495step0Labels = mixedMoment B raw23495step1 raw23495step1Labels := by
      have hz : ∀ j, raw23495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23495step1 = (fun i j => raw23495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23495step1 raw23495step0; decide +kernel
      have hl : raw23495step1Labels = raw23495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23495step0 raw23495step0Labels permutation80 hz
    mixedMoment B raw23495step1 raw23495step1Labels = mixedMoment B raw23495step2 raw23495step2Labels := by
      have hz : ∀ j, raw23495step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23495step2 = (fun i j => raw23495step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23495step2 raw23495step1; decide +kernel
      have hl : raw23495step2Labels = raw23495step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23495step1 raw23495step1Labels permutation14 hz
    mixedMoment B raw23495step2 raw23495step2Labels = mixedMoment B raw23495step3 raw23495step3Labels := by
      have ha : raw23495step3 = (fun i j => raw23495step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23495step3 raw23495step2; decide +kernel
      have hl : raw23495step3Labels = raw23495step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23495step2 raw23495step2Labels permutation3 permutation6
    _ = mixedMoment B node1093 node1093Labels := by rfl

def raw23496 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23496step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -3, 2], ![-1, -1, 2]]
def raw23496step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23496step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -1, -1], ![2, 1, -3]]
def raw23496step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23496 raw23496Labels = mixedMoment B node863 node863Labels := by
  calc
    mixedMoment B raw23496 raw23496Labels = mixedMoment B raw23496step0 raw23496step0Labels := by
      have hz : ∀ j, raw23496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23496step0 = (fun i j => raw23496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23496step0 raw23496; decide +kernel
      have hl : raw23496step0Labels = raw23496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23496 raw23496Labels permutation434 hz
    mixedMoment B raw23496step0 raw23496step0Labels = mixedMoment B raw23496step1 raw23496step1Labels := by
      have hz : ∀ j, raw23496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23496step1 = (fun i j => raw23496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23496step1 raw23496step0; decide +kernel
      have hl : raw23496step1Labels = raw23496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23496step0 raw23496step0Labels permutation80 hz
    mixedMoment B raw23496step1 raw23496step1Labels = mixedMoment B raw23496step2 raw23496step2Labels := by
      have hz : ∀ j, raw23496step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23496step2 = (fun i j => raw23496step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23496step2 raw23496step1; decide +kernel
      have hl : raw23496step2Labels = raw23496step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23496step1 raw23496step1Labels permutation14 hz
    mixedMoment B raw23496step2 raw23496step2Labels = mixedMoment B raw23496step3 raw23496step3Labels := by
      have ha : raw23496step3 = (fun i j => raw23496step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23496step3 raw23496step2; decide +kernel
      have hl : raw23496step3Labels = raw23496step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23496step2 raw23496step2Labels permutation3 permutation6
    _ = mixedMoment B node863 node863Labels := by rfl

def raw23497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23497 raw23497Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw23497 raw23497Labels = mixedMoment B raw23497step0 raw23497step0Labels := by
      have hz : ∀ j, raw23497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23497step0 = (fun i j => raw23497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23497step0 raw23497; decide +kernel
      have hl : raw23497step0Labels = raw23497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23497 raw23497Labels permutation434 hz
    mixedMoment B raw23497step0 raw23497step0Labels = mixedMoment B raw23497step1 raw23497step1Labels := by
      have hz : ∀ j, raw23497step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23497step1 = (fun i j => raw23497step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23497step1 raw23497step0; decide +kernel
      have hl : raw23497step1Labels = raw23497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23497step0 raw23497step0Labels permutation80 hz
    mixedMoment B raw23497step1 raw23497step1Labels = mixedMoment B raw23497step2 raw23497step2Labels := by
      have ha : raw23497step2 = (fun i j => raw23497step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23497step2 raw23497step1; decide +kernel
      have hl : raw23497step2Labels = raw23497step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23497step1 raw23497step1Labels permutation9 permutation6
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw23498 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23498step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw23498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23498 raw23498Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw23498 raw23498Labels = mixedMoment B raw23498step0 raw23498step0Labels := by
      have hz : ∀ j, raw23498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23498step0 = (fun i j => raw23498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23498step0 raw23498; decide +kernel
      have hl : raw23498step0Labels = raw23498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23498 raw23498Labels permutation434 hz
    mixedMoment B raw23498step0 raw23498step0Labels = mixedMoment B raw23498step1 raw23498step1Labels := by
      have hz : ∀ j, raw23498step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23498step1 = (fun i j => raw23498step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23498step1 raw23498step0; decide +kernel
      have hl : raw23498step1Labels = raw23498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23498step0 raw23498step0Labels permutation56 hz
    mixedMoment B raw23498step1 raw23498step1Labels = mixedMoment B raw23498step2 raw23498step2Labels := by
      have ha : raw23498step2 = (fun i j => raw23498step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23498step2 raw23498step1; decide +kernel
      have hl : raw23498step2Labels = raw23498step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23498step1 raw23498step1Labels permutation9 permutation6
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw23499 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23499step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23499step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23499 raw23499Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw23499 raw23499Labels = mixedMoment B raw23499step0 raw23499step0Labels := by
      have hz : ∀ j, raw23499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23499step0 = (fun i j => raw23499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23499step0 raw23499; decide +kernel
      have hl : raw23499step0Labels = raw23499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23499 raw23499Labels permutation434 hz
    mixedMoment B raw23499step0 raw23499step0Labels = mixedMoment B raw23499step1 raw23499step1Labels := by
      have hz : ∀ j, raw23499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23499step1 = (fun i j => raw23499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23499step1 raw23499step0; decide +kernel
      have hl : raw23499step1Labels = raw23499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23499step0 raw23499step0Labels permutation80 hz
    mixedMoment B raw23499step1 raw23499step1Labels = mixedMoment B raw23499step2 raw23499step2Labels := by
      have ha : raw23499step2 = (fun i j => raw23499step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23499step2 raw23499step1; decide +kernel
      have hl : raw23499step2Labels = raw23499step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23499step1 raw23499step1Labels permutation8 permutation7
    mixedMoment B raw23499step2 raw23499step2Labels = mixedMoment B raw23499step3 raw23499step3Labels := by
      have ha : raw23499step3 = raw23499step2 := by apply Matrix.ext; unfold raw23499step3 raw23499step2; decide +kernel
      have hl : raw23499step2Labels = labelEmbedding1 ∘ raw23499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23499step2 raw23499step2Labels raw23499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw23500 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23500step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23500step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23500step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23500step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23500 raw23500Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw23500 raw23500Labels = mixedMoment B raw23500step0 raw23500step0Labels := by
      have hz : ∀ j, raw23500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23500step0 = (fun i j => raw23500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23500step0 raw23500; decide +kernel
      have hl : raw23500step0Labels = raw23500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23500 raw23500Labels permutation434 hz
    mixedMoment B raw23500step0 raw23500step0Labels = mixedMoment B raw23500step1 raw23500step1Labels := by
      have hz : ∀ j, raw23500step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23500step1 = (fun i j => raw23500step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23500step1 raw23500step0; decide +kernel
      have hl : raw23500step1Labels = raw23500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23500step0 raw23500step0Labels permutation56 hz
    mixedMoment B raw23500step1 raw23500step1Labels = mixedMoment B raw23500step2 raw23500step2Labels := by
      have ha : raw23500step2 = (fun i j => raw23500step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23500step2 raw23500step1; decide +kernel
      have hl : raw23500step2Labels = raw23500step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23500step1 raw23500step1Labels permutation8 permutation7
    mixedMoment B raw23500step2 raw23500step2Labels = mixedMoment B raw23500step3 raw23500step3Labels := by
      have ha : raw23500step3 = raw23500step2 := by apply Matrix.ext; unfold raw23500step3 raw23500step2; decide +kernel
      have hl : raw23500step2Labels = labelEmbedding1 ∘ raw23500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23500step2 raw23500step2Labels raw23500step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw23501 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23501step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -3, 2], ![-3, 1, 2]]
def raw23501step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23501step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw23501step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23501step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw23501step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23501 raw23501Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw23501 raw23501Labels = mixedMoment B raw23501step0 raw23501step0Labels := by
      have hz : ∀ j, raw23501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23501step0 = (fun i j => raw23501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23501step0 raw23501; decide +kernel
      have hl : raw23501step0Labels = raw23501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23501 raw23501Labels permutation434 hz
    mixedMoment B raw23501step0 raw23501step0Labels = mixedMoment B raw23501step1 raw23501step1Labels := by
      have hz : ∀ j, raw23501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23501step1 = (fun i j => raw23501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23501step1 raw23501step0; decide +kernel
      have hl : raw23501step1Labels = raw23501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23501step0 raw23501step0Labels permutation80 hz
    mixedMoment B raw23501step1 raw23501step1Labels = mixedMoment B raw23501step2 raw23501step2Labels := by
      have hz : ∀ j, raw23501step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23501step2 = (fun i j => raw23501step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23501step2 raw23501step1; decide +kernel
      have hl : raw23501step2Labels = raw23501step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23501step1 raw23501step1Labels permutation14 hz
    mixedMoment B raw23501step2 raw23501step2Labels = mixedMoment B raw23501step3 raw23501step3Labels := by
      have ha : raw23501step3 = (fun i j => raw23501step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23501step3 raw23501step2; decide +kernel
      have hl : raw23501step3Labels = raw23501step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23501step2 raw23501step2Labels permutation2 permutation7
    mixedMoment B raw23501step3 raw23501step3Labels = mixedMoment B raw23501step4 raw23501step4Labels := by
      have ha : raw23501step4 = raw23501step3 := by apply Matrix.ext; unfold raw23501step4 raw23501step3; decide +kernel
      have hl : raw23501step3Labels = labelEmbedding1 ∘ raw23501step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23501step3 raw23501step3Labels raw23501step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw23502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23502step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw23502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23502step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23502step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23502step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23502step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23502 raw23502Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw23502 raw23502Labels = mixedMoment B raw23502step0 raw23502step0Labels := by
      have hz : ∀ j, raw23502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23502step0 = (fun i j => raw23502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23502step0 raw23502; decide +kernel
      have hl : raw23502step0Labels = raw23502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23502 raw23502Labels permutation434 hz
    mixedMoment B raw23502step0 raw23502step0Labels = mixedMoment B raw23502step1 raw23502step1Labels := by
      have hz : ∀ j, raw23502step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23502step1 = (fun i j => raw23502step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23502step1 raw23502step0; decide +kernel
      have hl : raw23502step1Labels = raw23502step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23502step0 raw23502step0Labels permutation56 hz
    mixedMoment B raw23502step1 raw23502step1Labels = mixedMoment B raw23502step2 raw23502step2Labels := by
      have ha : raw23502step2 = (fun i j => raw23502step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23502step2 raw23502step1; decide +kernel
      have hl : raw23502step2Labels = raw23502step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23502step1 raw23502step1Labels permutation12 permutation5
    mixedMoment B raw23502step2 raw23502step2Labels = mixedMoment B raw23502step3 raw23502step3Labels := by
      have ha : raw23502step3 = -raw23502step2 := by apply Matrix.ext; change ∀ i j, raw23502step3 i j = -(raw23502step2 i j); unfold raw23502step3 raw23502step2; decide +kernel
      have hl : raw23502step3Labels = raw23502step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23502step3 raw23502step3Labels = mixedMoment B raw23502step4 raw23502step4Labels := by
      have ha : raw23502step4 = raw23502step3 := by apply Matrix.ext; unfold raw23502step4 raw23502step3; decide +kernel
      have hl : raw23502step3Labels = labelEmbedding1 ∘ raw23502step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23502step3 raw23502step3Labels raw23502step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

def raw23503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23503 raw23503Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23503 raw23503Labels = mixedMoment B raw23503step0 raw23503step0Labels := by
      have hz : ∀ j, raw23503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23503step0 = (fun i j => raw23503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23503step0 raw23503; decide +kernel
      have hl : raw23503step0Labels = raw23503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23503 raw23503Labels permutation434 hz
    mixedMoment B raw23503step0 raw23503step0Labels = mixedMoment B raw23503step1 raw23503step1Labels := by
      have ha : raw23503step1 = (fun i j => raw23503step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23503step1 raw23503step0; decide +kernel
      have hl : raw23503step1Labels = raw23503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23503step0 raw23503step0Labels permutation38 permutation7
    mixedMoment B raw23503step1 raw23503step1Labels = mixedMoment B raw23503step2 raw23503step2Labels := by
      have ha : raw23503step2 = raw23503step1 := by apply Matrix.ext; unfold raw23503step2 raw23503step1; decide +kernel
      have hl : raw23503step1Labels = labelEmbedding1 ∘ raw23503step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23503step1 raw23503step1Labels raw23503step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23504 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23504 raw23504Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23504 raw23504Labels = mixedMoment B raw23504step0 raw23504step0Labels := by
      have hz : ∀ j, raw23504 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23504step0 = (fun i j => raw23504 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23504step0 raw23504; decide +kernel
      have hl : raw23504step0Labels = raw23504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23504 raw23504Labels permutation265 hz
    mixedMoment B raw23504step0 raw23504step0Labels = mixedMoment B raw23504step1 raw23504step1Labels := by
      have ha : raw23504step1 = (fun i j => raw23504step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23504step1 raw23504step0; decide +kernel
      have hl : raw23504step1Labels = raw23504step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23504step0 raw23504step0Labels permutation32 permutation7
    mixedMoment B raw23504step1 raw23504step1Labels = mixedMoment B raw23504step2 raw23504step2Labels := by
      have ha : raw23504step2 = raw23504step1 := by apply Matrix.ext; unfold raw23504step2 raw23504step1; decide +kernel
      have hl : raw23504step1Labels = labelEmbedding1 ∘ raw23504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23504step1 raw23504step1Labels raw23504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23505 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23505step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23505 raw23505Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw23505 raw23505Labels = mixedMoment B raw23505step0 raw23505step0Labels := by
      have hz : ∀ j, raw23505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23505step0 = (fun i j => raw23505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23505step0 raw23505; decide +kernel
      have hl : raw23505step0Labels = raw23505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23505 raw23505Labels permutation434 hz
    mixedMoment B raw23505step0 raw23505step0Labels = mixedMoment B raw23505step1 raw23505step1Labels := by
      have hz : ∀ j, raw23505step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23505step1 = (fun i j => raw23505step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23505step1 raw23505step0; decide +kernel
      have hl : raw23505step1Labels = raw23505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23505step0 raw23505step0Labels permutation56 hz
    mixedMoment B raw23505step1 raw23505step1Labels = mixedMoment B raw23505step2 raw23505step2Labels := by
      have ha : raw23505step2 = (fun i j => raw23505step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23505step2 raw23505step1; decide +kernel
      have hl : raw23505step2Labels = raw23505step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23505step1 raw23505step1Labels permutation8 permutation7
    mixedMoment B raw23505step2 raw23505step2Labels = mixedMoment B raw23505step3 raw23505step3Labels := by
      have ha : raw23505step3 = raw23505step2 := by apply Matrix.ext; unfold raw23505step3 raw23505step2; decide +kernel
      have hl : raw23505step2Labels = labelEmbedding1 ∘ raw23505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23505step2 raw23505step2Labels raw23505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1418 node1418Labels := by rfl

def raw23506 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23506step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw23506step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23506step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23506step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23506step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23506 raw23506Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw23506 raw23506Labels = mixedMoment B raw23506step0 raw23506step0Labels := by
      have hz : ∀ j, raw23506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23506step0 = (fun i j => raw23506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23506step0 raw23506; decide +kernel
      have hl : raw23506step0Labels = raw23506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23506 raw23506Labels permutation346 hz
    mixedMoment B raw23506step0 raw23506step0Labels = mixedMoment B raw23506step1 raw23506step1Labels := by
      have hz : ∀ j, raw23506step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23506step1 = (fun i j => raw23506step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23506step1 raw23506step0; decide +kernel
      have hl : raw23506step1Labels = raw23506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23506step0 raw23506step0Labels permutation56 hz
    mixedMoment B raw23506step1 raw23506step1Labels = mixedMoment B raw23506step2 raw23506step2Labels := by
      have ha : raw23506step2 = (fun i j => raw23506step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23506step2 raw23506step1; decide +kernel
      have hl : raw23506step2Labels = raw23506step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23506step1 raw23506step1Labels permutation12 permutation5
    mixedMoment B raw23506step2 raw23506step2Labels = mixedMoment B raw23506step3 raw23506step3Labels := by
      have ha : raw23506step3 = -raw23506step2 := by apply Matrix.ext; change ∀ i j, raw23506step3 i j = -(raw23506step2 i j); unfold raw23506step3 raw23506step2; decide +kernel
      have hl : raw23506step3Labels = raw23506step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23506step3 raw23506step3Labels = mixedMoment B raw23506step4 raw23506step4Labels := by
      have ha : raw23506step4 = raw23506step3 := by apply Matrix.ext; unfold raw23506step4 raw23506step3; decide +kernel
      have hl : raw23506step3Labels = labelEmbedding1 ∘ raw23506step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23506step3 raw23506step3Labels raw23506step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

def raw23507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23507 raw23507Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23507 raw23507Labels = mixedMoment B raw23507step0 raw23507step0Labels := by
      have hz : ∀ j, raw23507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23507step0 = (fun i j => raw23507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23507step0 raw23507; decide +kernel
      have hl : raw23507step0Labels = raw23507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23507 raw23507Labels permutation346 hz
    mixedMoment B raw23507step0 raw23507step0Labels = mixedMoment B raw23507step1 raw23507step1Labels := by
      have ha : raw23507step1 = (fun i j => raw23507step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23507step1 raw23507step0; decide +kernel
      have hl : raw23507step1Labels = raw23507step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23507step0 raw23507step0Labels permutation38 permutation7
    mixedMoment B raw23507step1 raw23507step1Labels = mixedMoment B raw23507step2 raw23507step2Labels := by
      have ha : raw23507step2 = raw23507step1 := by apply Matrix.ext; unfold raw23507step2 raw23507step1; decide +kernel
      have hl : raw23507step1Labels = labelEmbedding1 ∘ raw23507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23507step1 raw23507step1Labels raw23507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23508step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23508 raw23508Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23508 raw23508Labels = mixedMoment B raw23508step0 raw23508step0Labels := by
      have hz : ∀ j, raw23508 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23508step0 = (fun i j => raw23508 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23508step0 raw23508; decide +kernel
      have hl : raw23508step0Labels = raw23508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23508 raw23508Labels permutation265 hz
    mixedMoment B raw23508step0 raw23508step0Labels = mixedMoment B raw23508step1 raw23508step1Labels := by
      have ha : raw23508step1 = (fun i j => raw23508step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23508step1 raw23508step0; decide +kernel
      have hl : raw23508step1Labels = raw23508step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23508step0 raw23508step0Labels permutation38 permutation7
    mixedMoment B raw23508step1 raw23508step1Labels = mixedMoment B raw23508step2 raw23508step2Labels := by
      have ha : raw23508step2 = raw23508step1 := by apply Matrix.ext; unfold raw23508step2 raw23508step1; decide +kernel
      have hl : raw23508step1Labels = labelEmbedding1 ∘ raw23508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23508step1 raw23508step1Labels raw23508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23509step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23509 raw23509Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw23509 raw23509Labels = mixedMoment B raw23509step0 raw23509step0Labels := by
      have hz : ∀ j, raw23509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23509step0 = (fun i j => raw23509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23509step0 raw23509; decide +kernel
      have hl : raw23509step0Labels = raw23509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23509 raw23509Labels permutation346 hz
    mixedMoment B raw23509step0 raw23509step0Labels = mixedMoment B raw23509step1 raw23509step1Labels := by
      have hz : ∀ j, raw23509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23509step1 = (fun i j => raw23509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23509step1 raw23509step0; decide +kernel
      have hl : raw23509step1Labels = raw23509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23509step0 raw23509step0Labels permutation56 hz
    mixedMoment B raw23509step1 raw23509step1Labels = mixedMoment B raw23509step2 raw23509step2Labels := by
      have ha : raw23509step2 = (fun i j => raw23509step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23509step2 raw23509step1; decide +kernel
      have hl : raw23509step2Labels = raw23509step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23509step1 raw23509step1Labels permutation8 permutation7
    mixedMoment B raw23509step2 raw23509step2Labels = mixedMoment B raw23509step3 raw23509step3Labels := by
      have ha : raw23509step3 = raw23509step2 := by apply Matrix.ext; unfold raw23509step3 raw23509step2; decide +kernel
      have hl : raw23509step2Labels = labelEmbedding1 ∘ raw23509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23509step2 raw23509step2Labels raw23509step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1418 node1418Labels := by rfl

def raw23510 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23510step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -4, 2], ![-2, 0, 2]]
def raw23510step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw23510step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23510step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def raw23510step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23510 raw23510Labels = mixedMoment B node1285 node1285Labels := by
  calc
    mixedMoment B raw23510 raw23510Labels = mixedMoment B raw23510step0 raw23510step0Labels := by
      have hz : ∀ j, raw23510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23510step0 = (fun i j => raw23510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23510step0 raw23510; decide +kernel
      have hl : raw23510step0Labels = raw23510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23510 raw23510Labels permutation434 hz
    mixedMoment B raw23510step0 raw23510step0Labels = mixedMoment B raw23510step1 raw23510step1Labels := by
      have hz : ∀ j, raw23510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23510step1 = (fun i j => raw23510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23510step1 raw23510step0; decide +kernel
      have hl : raw23510step1Labels = raw23510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23510step0 raw23510step0Labels permutation80 hz
    mixedMoment B raw23510step1 raw23510step1Labels = mixedMoment B raw23510step2 raw23510step2Labels := by
      have hz : ∀ j, raw23510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23510step2 = (fun i j => raw23510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23510step2 raw23510step1; decide +kernel
      have hl : raw23510step2Labels = raw23510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23510step1 raw23510step1Labels permutation14 hz
    mixedMoment B raw23510step2 raw23510step2Labels = mixedMoment B raw23510step3 raw23510step3Labels := by
      have ha : raw23510step3 = (fun i j => raw23510step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23510step3 raw23510step2; decide +kernel
      have hl : raw23510step3Labels = raw23510step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23510step2 raw23510step2Labels permutation5 permutation5
    mixedMoment B raw23510step3 raw23510step3Labels = mixedMoment B raw23510step4 raw23510step4Labels := by
      have ha : raw23510step4 = raw23510step3 := by apply Matrix.ext; unfold raw23510step4 raw23510step3; decide +kernel
      have hl : raw23510step3Labels = labelEmbedding1 ∘ raw23510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23510step3 raw23510step3Labels raw23510step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1285 node1285Labels := by rfl

def raw23511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23511step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23511step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23511 raw23511Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw23511 raw23511Labels = mixedMoment B raw23511step0 raw23511step0Labels := by
      have hz : ∀ j, raw23511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23511step0 = (fun i j => raw23511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23511step0 raw23511; decide +kernel
      have hl : raw23511step0Labels = raw23511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23511 raw23511Labels permutation434 hz
    mixedMoment B raw23511step0 raw23511step0Labels = mixedMoment B raw23511step1 raw23511step1Labels := by
      have hz : ∀ j, raw23511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23511step1 = (fun i j => raw23511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23511step1 raw23511step0; decide +kernel
      have hl : raw23511step1Labels = raw23511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23511step0 raw23511step0Labels permutation80 hz
    mixedMoment B raw23511step1 raw23511step1Labels = mixedMoment B raw23511step2 raw23511step2Labels := by
      have ha : raw23511step2 = (fun i j => raw23511step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23511step2 raw23511step1; decide +kernel
      have hl : raw23511step2Labels = raw23511step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23511step1 raw23511step1Labels permutation25 permutation5
    mixedMoment B raw23511step2 raw23511step2Labels = mixedMoment B raw23511step3 raw23511step3Labels := by
      have ha : raw23511step3 = raw23511step2 := by apply Matrix.ext; unfold raw23511step3 raw23511step2; decide +kernel
      have hl : raw23511step2Labels = labelEmbedding1 ∘ raw23511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23511step2 raw23511step2Labels raw23511step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1282 node1282Labels := by rfl

def raw23512 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23512step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23512step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23512step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23512 raw23512Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw23512 raw23512Labels = mixedMoment B raw23512step0 raw23512step0Labels := by
      have hz : ∀ j, raw23512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23512step0 = (fun i j => raw23512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23512step0 raw23512; decide +kernel
      have hl : raw23512step0Labels = raw23512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23512 raw23512Labels permutation434 hz
    mixedMoment B raw23512step0 raw23512step0Labels = mixedMoment B raw23512step1 raw23512step1Labels := by
      have hz : ∀ j, raw23512step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23512step1 = (fun i j => raw23512step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23512step1 raw23512step0; decide +kernel
      have hl : raw23512step1Labels = raw23512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23512step0 raw23512step0Labels permutation56 hz
    mixedMoment B raw23512step1 raw23512step1Labels = mixedMoment B raw23512step2 raw23512step2Labels := by
      have ha : raw23512step2 = (fun i j => raw23512step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23512step2 raw23512step1; decide +kernel
      have hl : raw23512step2Labels = raw23512step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23512step1 raw23512step1Labels permutation25 permutation5
    mixedMoment B raw23512step2 raw23512step2Labels = mixedMoment B raw23512step3 raw23512step3Labels := by
      have ha : raw23512step3 = raw23512step2 := by apply Matrix.ext; unfold raw23512step3 raw23512step2; decide +kernel
      have hl : raw23512step2Labels = labelEmbedding1 ∘ raw23512step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23512step2 raw23512step2Labels raw23512step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1282 node1282Labels := by rfl

def raw23513 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23513step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw23513step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23513step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw23513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23513 raw23513Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw23513 raw23513Labels = mixedMoment B raw23513step0 raw23513step0Labels := by
      have hz : ∀ j, raw23513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23513step0 = (fun i j => raw23513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23513step0 raw23513; decide +kernel
      have hl : raw23513step0Labels = raw23513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23513 raw23513Labels permutation346 hz
    mixedMoment B raw23513step0 raw23513step0Labels = mixedMoment B raw23513step1 raw23513step1Labels := by
      have hz : ∀ j, raw23513step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23513step1 = (fun i j => raw23513step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23513step1 raw23513step0; decide +kernel
      have hl : raw23513step1Labels = raw23513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23513step0 raw23513step0Labels permutation56 hz
    mixedMoment B raw23513step1 raw23513step1Labels = mixedMoment B raw23513step2 raw23513step2Labels := by
      have ha : raw23513step2 = (fun i j => raw23513step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23513step2 raw23513step1; decide +kernel
      have hl : raw23513step2Labels = raw23513step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23513step1 raw23513step1Labels permutation25 permutation5
    mixedMoment B raw23513step2 raw23513step2Labels = mixedMoment B raw23513step3 raw23513step3Labels := by
      have ha : raw23513step3 = raw23513step2 := by apply Matrix.ext; unfold raw23513step3 raw23513step2; decide +kernel
      have hl : raw23513step2Labels = labelEmbedding1 ∘ raw23513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23513step2 raw23513step2Labels raw23513step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1282 node1282Labels := by rfl

def raw23514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23514step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw23514step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23514step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -4, 2], ![-3, 1, 2]]
def raw23514step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23514step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw23514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23514step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw23514step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23514 raw23514Labels = mixedMoment B node1309 node1309Labels := by
  calc
    mixedMoment B raw23514 raw23514Labels = mixedMoment B raw23514step0 raw23514step0Labels := by
      have hz : ∀ j, raw23514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23514step0 = (fun i j => raw23514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23514step0 raw23514; decide +kernel
      have hl : raw23514step0Labels = raw23514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23514 raw23514Labels permutation434 hz
    mixedMoment B raw23514step0 raw23514step0Labels = mixedMoment B raw23514step1 raw23514step1Labels := by
      have hz : ∀ j, raw23514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23514step1 = (fun i j => raw23514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23514step1 raw23514step0; decide +kernel
      have hl : raw23514step1Labels = raw23514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23514step0 raw23514step0Labels permutation80 hz
    mixedMoment B raw23514step1 raw23514step1Labels = mixedMoment B raw23514step2 raw23514step2Labels := by
      have hz : ∀ j, raw23514step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23514step2 = (fun i j => raw23514step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23514step2 raw23514step1; decide +kernel
      have hl : raw23514step2Labels = raw23514step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23514step1 raw23514step1Labels permutation14 hz
    mixedMoment B raw23514step2 raw23514step2Labels = mixedMoment B raw23514step3 raw23514step3Labels := by
      have ha : raw23514step3 = (fun i j => raw23514step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23514step3 raw23514step2; decide +kernel
      have hl : raw23514step3Labels = raw23514step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23514step2 raw23514step2Labels permutation5 permutation5
    mixedMoment B raw23514step3 raw23514step3Labels = mixedMoment B raw23514step4 raw23514step4Labels := by
      have ha : raw23514step4 = raw23514step3 := by apply Matrix.ext; unfold raw23514step4 raw23514step3; decide +kernel
      have hl : raw23514step3Labels = labelEmbedding1 ∘ raw23514step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23514step3 raw23514step3Labels raw23514step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1309 node1309Labels := by rfl

def raw23515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23515step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23515step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -3, 2], ![-1, -1, 2]]
def raw23515step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23515step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -4, 0], ![-1, 2, -1], ![-3, 2, 1]]
def raw23515step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23515step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![3, -2, -1]]
def raw23515step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23515step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![3, -2, -1]]
def raw23515step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23515 raw23515Labels = mixedMoment B node1487 node1487Labels := by
  calc
    mixedMoment B raw23515 raw23515Labels = mixedMoment B raw23515step0 raw23515step0Labels := by
      have hz : ∀ j, raw23515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23515step0 = (fun i j => raw23515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23515step0 raw23515; decide +kernel
      have hl : raw23515step0Labels = raw23515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23515 raw23515Labels permutation434 hz
    mixedMoment B raw23515step0 raw23515step0Labels = mixedMoment B raw23515step1 raw23515step1Labels := by
      have hz : ∀ j, raw23515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23515step1 = (fun i j => raw23515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23515step1 raw23515step0; decide +kernel
      have hl : raw23515step1Labels = raw23515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23515step0 raw23515step0Labels permutation80 hz
    mixedMoment B raw23515step1 raw23515step1Labels = mixedMoment B raw23515step2 raw23515step2Labels := by
      have hz : ∀ j, raw23515step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23515step2 = (fun i j => raw23515step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23515step2 raw23515step1; decide +kernel
      have hl : raw23515step2Labels = raw23515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23515step1 raw23515step1Labels permutation14 hz
    mixedMoment B raw23515step2 raw23515step2Labels = mixedMoment B raw23515step3 raw23515step3Labels := by
      have ha : raw23515step3 = (fun i j => raw23515step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23515step3 raw23515step2; decide +kernel
      have hl : raw23515step3Labels = raw23515step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23515step2 raw23515step2Labels permutation3 permutation5
    mixedMoment B raw23515step3 raw23515step3Labels = mixedMoment B raw23515step4 raw23515step4Labels := by
      have ha : raw23515step4 = -raw23515step3 := by apply Matrix.ext; change ∀ i j, raw23515step4 i j = -(raw23515step3 i j); unfold raw23515step4 raw23515step3; decide +kernel
      have hl : raw23515step4Labels = raw23515step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23515step4 raw23515step4Labels = mixedMoment B raw23515step5 raw23515step5Labels := by
      have ha : raw23515step5 = raw23515step4 := by apply Matrix.ext; unfold raw23515step5 raw23515step4; decide +kernel
      have hl : raw23515step4Labels = labelEmbedding1 ∘ raw23515step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23515step4 raw23515step4Labels raw23515step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1487 node1487Labels := by rfl

def raw23516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23516step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw23516step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw23516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23516 raw23516Labels = mixedMoment B node1430 node1430Labels := by
  calc
    mixedMoment B raw23516 raw23516Labels = mixedMoment B raw23516step0 raw23516step0Labels := by
      have hz : ∀ j, raw23516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23516step0 = (fun i j => raw23516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23516step0 raw23516; decide +kernel
      have hl : raw23516step0Labels = raw23516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23516 raw23516Labels permutation434 hz
    mixedMoment B raw23516step0 raw23516step0Labels = mixedMoment B raw23516step1 raw23516step1Labels := by
      have hz : ∀ j, raw23516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23516step1 = (fun i j => raw23516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23516step1 raw23516step0; decide +kernel
      have hl : raw23516step1Labels = raw23516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23516step0 raw23516step0Labels permutation80 hz
    mixedMoment B raw23516step1 raw23516step1Labels = mixedMoment B raw23516step2 raw23516step2Labels := by
      have ha : raw23516step2 = (fun i j => raw23516step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23516step2 raw23516step1; decide +kernel
      have hl : raw23516step2Labels = raw23516step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23516step1 raw23516step1Labels permutation8 permutation7
    mixedMoment B raw23516step2 raw23516step2Labels = mixedMoment B raw23516step3 raw23516step3Labels := by
      have ha : raw23516step3 = raw23516step2 := by apply Matrix.ext; unfold raw23516step3 raw23516step2; decide +kernel
      have hl : raw23516step2Labels = labelEmbedding1 ∘ raw23516step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23516step2 raw23516step2Labels raw23516step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1430 node1430Labels := by rfl

def raw23517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23517step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw23517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw23517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23517 raw23517Labels = mixedMoment B node1430 node1430Labels := by
  calc
    mixedMoment B raw23517 raw23517Labels = mixedMoment B raw23517step0 raw23517step0Labels := by
      have hz : ∀ j, raw23517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23517step0 = (fun i j => raw23517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23517step0 raw23517; decide +kernel
      have hl : raw23517step0Labels = raw23517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23517 raw23517Labels permutation434 hz
    mixedMoment B raw23517step0 raw23517step0Labels = mixedMoment B raw23517step1 raw23517step1Labels := by
      have hz : ∀ j, raw23517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23517step1 = (fun i j => raw23517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23517step1 raw23517step0; decide +kernel
      have hl : raw23517step1Labels = raw23517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23517step0 raw23517step0Labels permutation56 hz
    mixedMoment B raw23517step1 raw23517step1Labels = mixedMoment B raw23517step2 raw23517step2Labels := by
      have ha : raw23517step2 = (fun i j => raw23517step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23517step2 raw23517step1; decide +kernel
      have hl : raw23517step2Labels = raw23517step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23517step1 raw23517step1Labels permutation8 permutation7
    mixedMoment B raw23517step2 raw23517step2Labels = mixedMoment B raw23517step3 raw23517step3Labels := by
      have ha : raw23517step3 = raw23517step2 := by apply Matrix.ext; unfold raw23517step3 raw23517step2; decide +kernel
      have hl : raw23517step2Labels = labelEmbedding1 ∘ raw23517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23517step2 raw23517step2Labels raw23517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1430 node1430Labels := by rfl

def raw23518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23518 raw23518Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23518 raw23518Labels = mixedMoment B raw23518step0 raw23518step0Labels := by
      have hz : ∀ j, raw23518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23518step0 = (fun i j => raw23518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23518step0 raw23518; decide +kernel
      have hl : raw23518step0Labels = raw23518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23518 raw23518Labels permutation434 hz
    mixedMoment B raw23518step0 raw23518step0Labels = mixedMoment B raw23518step1 raw23518step1Labels := by
      have hz : ∀ j, raw23518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23518step1 = (fun i j => raw23518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23518step1 raw23518step0; decide +kernel
      have hl : raw23518step1Labels = raw23518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23518step0 raw23518step0Labels permutation80 hz
    mixedMoment B raw23518step1 raw23518step1Labels = mixedMoment B raw23518step2 raw23518step2Labels := by
      have ha : raw23518step2 = (fun i j => raw23518step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23518step2 raw23518step1; decide +kernel
      have hl : raw23518step2Labels = raw23518step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23518step1 raw23518step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw23519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23519 raw23519Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23519 raw23519Labels = mixedMoment B raw23519step0 raw23519step0Labels := by
      have hz : ∀ j, raw23519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23519step0 = (fun i j => raw23519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23519step0 raw23519; decide +kernel
      have hl : raw23519step0Labels = raw23519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23519 raw23519Labels permutation434 hz
    mixedMoment B raw23519step0 raw23519step0Labels = mixedMoment B raw23519step1 raw23519step1Labels := by
      have ha : raw23519step1 = (fun i j => raw23519step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23519step1 raw23519step0; decide +kernel
      have hl : raw23519step1Labels = raw23519step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23519step0 raw23519step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23520 raw23520Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23520 raw23520Labels = mixedMoment B raw23520step0 raw23520step0Labels := by
      have hz : ∀ j, raw23520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23520step0 = (fun i j => raw23520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23520step0 raw23520; decide +kernel
      have hl : raw23520step0Labels = raw23520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23520 raw23520Labels permutation346 hz
    mixedMoment B raw23520step0 raw23520step0Labels = mixedMoment B raw23520step1 raw23520step1Labels := by
      have ha : raw23520step1 = (fun i j => raw23520step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23520step1 raw23520step0; decide +kernel
      have hl : raw23520step1Labels = raw23520step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23520step0 raw23520step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23521 raw23521Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23521 raw23521Labels = mixedMoment B raw23521step0 raw23521step0Labels := by
      have hz : ∀ j, raw23521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23521step0 = (fun i j => raw23521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23521step0 raw23521; decide +kernel
      have hl : raw23521step0Labels = raw23521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23521 raw23521Labels permutation434 hz
    mixedMoment B raw23521step0 raw23521step0Labels = mixedMoment B raw23521step1 raw23521step1Labels := by
      have hz : ∀ j, raw23521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23521step1 = (fun i j => raw23521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23521step1 raw23521step0; decide +kernel
      have hl : raw23521step1Labels = raw23521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23521step0 raw23521step0Labels permutation80 hz
    mixedMoment B raw23521step1 raw23521step1Labels = mixedMoment B raw23521step2 raw23521step2Labels := by
      have ha : raw23521step2 = (fun i j => raw23521step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23521step2 raw23521step1; decide +kernel
      have hl : raw23521step2Labels = raw23521step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23521step1 raw23521step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw23522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23522 raw23522Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23522 raw23522Labels = mixedMoment B raw23522step0 raw23522step0Labels := by
      have hz : ∀ j, raw23522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23522step0 = (fun i j => raw23522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23522step0 raw23522; decide +kernel
      have hl : raw23522step0Labels = raw23522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23522 raw23522Labels permutation434 hz
    mixedMoment B raw23522step0 raw23522step0Labels = mixedMoment B raw23522step1 raw23522step1Labels := by
      have hz : ∀ j, raw23522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23522step1 = (fun i j => raw23522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23522step1 raw23522step0; decide +kernel
      have hl : raw23522step1Labels = raw23522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23522step0 raw23522step0Labels permutation56 hz
    mixedMoment B raw23522step1 raw23522step1Labels = mixedMoment B raw23522step2 raw23522step2Labels := by
      have ha : raw23522step2 = (fun i j => raw23522step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23522step2 raw23522step1; decide +kernel
      have hl : raw23522step2Labels = raw23522step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23522step1 raw23522step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw23523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23523 raw23523Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23523 raw23523Labels = mixedMoment B raw23523step0 raw23523step0Labels := by
      have hz : ∀ j, raw23523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23523step0 = (fun i j => raw23523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23523step0 raw23523; decide +kernel
      have hl : raw23523step0Labels = raw23523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23523 raw23523Labels permutation434 hz
    mixedMoment B raw23523step0 raw23523step0Labels = mixedMoment B raw23523step1 raw23523step1Labels := by
      have ha : raw23523step1 = (fun i j => raw23523step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23523step1 raw23523step0; decide +kernel
      have hl : raw23523step1Labels = raw23523step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23523step0 raw23523step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23524 raw23524Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23524 raw23524Labels = mixedMoment B raw23524step0 raw23524step0Labels := by
      have hz : ∀ j, raw23524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23524step0 = (fun i j => raw23524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23524step0 raw23524; decide +kernel
      have hl : raw23524step0Labels = raw23524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23524 raw23524Labels permutation265 hz
    mixedMoment B raw23524step0 raw23524step0Labels = mixedMoment B raw23524step1 raw23524step1Labels := by
      have ha : raw23524step1 = (fun i j => raw23524step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23524step1 raw23524step0; decide +kernel
      have hl : raw23524step1Labels = raw23524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23524step0 raw23524step0Labels permutation39 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23525 raw23525Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23525 raw23525Labels = mixedMoment B raw23525step0 raw23525step0Labels := by
      have hz : ∀ j, raw23525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23525step0 = (fun i j => raw23525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23525step0 raw23525; decide +kernel
      have hl : raw23525step0Labels = raw23525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23525 raw23525Labels permutation434 hz
    mixedMoment B raw23525step0 raw23525step0Labels = mixedMoment B raw23525step1 raw23525step1Labels := by
      have hz : ∀ j, raw23525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23525step1 = (fun i j => raw23525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23525step1 raw23525step0; decide +kernel
      have hl : raw23525step1Labels = raw23525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23525step0 raw23525step0Labels permutation56 hz
    mixedMoment B raw23525step1 raw23525step1Labels = mixedMoment B raw23525step2 raw23525step2Labels := by
      have ha : raw23525step2 = (fun i j => raw23525step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23525step2 raw23525step1; decide +kernel
      have hl : raw23525step2Labels = raw23525step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23525step1 raw23525step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw23526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23526 raw23526Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw23526 raw23526Labels = mixedMoment B raw23526step0 raw23526step0Labels := by
      have hz : ∀ j, raw23526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23526step0 = (fun i j => raw23526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23526step0 raw23526; decide +kernel
      have hl : raw23526step0Labels = raw23526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23526 raw23526Labels permutation346 hz
    mixedMoment B raw23526step0 raw23526step0Labels = mixedMoment B raw23526step1 raw23526step1Labels := by
      have hz : ∀ j, raw23526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23526step1 = (fun i j => raw23526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23526step1 raw23526step0; decide +kernel
      have hl : raw23526step1Labels = raw23526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23526step0 raw23526step0Labels permutation56 hz
    mixedMoment B raw23526step1 raw23526step1Labels = mixedMoment B raw23526step2 raw23526step2Labels := by
      have ha : raw23526step2 = (fun i j => raw23526step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23526step2 raw23526step1; decide +kernel
      have hl : raw23526step2Labels = raw23526step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23526step1 raw23526step1Labels permutation9 permutation2
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw23527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23527 raw23527Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23527 raw23527Labels = mixedMoment B raw23527step0 raw23527step0Labels := by
      have hz : ∀ j, raw23527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23527step0 = (fun i j => raw23527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23527step0 raw23527; decide +kernel
      have hl : raw23527step0Labels = raw23527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23527 raw23527Labels permutation346 hz
    mixedMoment B raw23527step0 raw23527step0Labels = mixedMoment B raw23527step1 raw23527step1Labels := by
      have ha : raw23527step1 = (fun i j => raw23527step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23527step1 raw23527step0; decide +kernel
      have hl : raw23527step1Labels = raw23527step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23527step0 raw23527step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23528 raw23528Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw23528 raw23528Labels = mixedMoment B raw23528step0 raw23528step0Labels := by
      have hz : ∀ j, raw23528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23528step0 = (fun i j => raw23528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23528step0 raw23528; decide +kernel
      have hl : raw23528step0Labels = raw23528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23528 raw23528Labels permutation265 hz
    mixedMoment B raw23528step0 raw23528step0Labels = mixedMoment B raw23528step1 raw23528step1Labels := by
      have ha : raw23528step1 = (fun i j => raw23528step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23528step1 raw23528step0; decide +kernel
      have hl : raw23528step1Labels = raw23528step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23528step0 raw23528step0Labels permutation33 permutation2
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw23529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23529 raw23529Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw23529 raw23529Labels = mixedMoment B raw23529step0 raw23529step0Labels := by
      have hz : ∀ j, raw23529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23529step0 = (fun i j => raw23529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23529step0 raw23529; decide +kernel
      have hl : raw23529step0Labels = raw23529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23529 raw23529Labels permutation346 hz
    mixedMoment B raw23529step0 raw23529step0Labels = mixedMoment B raw23529step1 raw23529step1Labels := by
      have hz : ∀ j, raw23529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23529step1 = (fun i j => raw23529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23529step1 raw23529step0; decide +kernel
      have hl : raw23529step1Labels = raw23529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23529step0 raw23529step0Labels permutation56 hz
    mixedMoment B raw23529step1 raw23529step1Labels = mixedMoment B raw23529step2 raw23529step2Labels := by
      have ha : raw23529step2 = (fun i j => raw23529step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23529step2 raw23529step1; decide +kernel
      have hl : raw23529step2Labels = raw23529step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23529step1 raw23529step1Labels permutation9 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw23530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw23530step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23530 raw23530Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw23530 raw23530Labels = mixedMoment B raw23530step0 raw23530step0Labels := by
      have hz : ∀ j, raw23530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23530step0 = (fun i j => raw23530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23530step0 raw23530; decide +kernel
      have hl : raw23530step0Labels = raw23530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530 raw23530Labels permutation434 hz
    mixedMoment B raw23530step0 raw23530step0Labels = mixedMoment B raw23530step1 raw23530step1Labels := by
      have hz : ∀ j, raw23530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23530step1 = (fun i j => raw23530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23530step1 raw23530step0; decide +kernel
      have hl : raw23530step1Labels = raw23530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530step0 raw23530step0Labels permutation80 hz
    mixedMoment B raw23530step1 raw23530step1Labels = mixedMoment B raw23530step2 raw23530step2Labels := by
      have hz : ∀ j, raw23530step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23530step2 = (fun i j => raw23530step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23530step2 raw23530step1; decide +kernel
      have hl : raw23530step2Labels = raw23530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23530step1 raw23530step1Labels permutation14 hz
    mixedMoment B raw23530step2 raw23530step2Labels = mixedMoment B raw23530step3 raw23530step3Labels := by
      have ha : raw23530step3 = (fun i j => raw23530step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23530step3 raw23530step2; decide +kernel
      have hl : raw23530step3Labels = raw23530step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23530step2 raw23530step2Labels permutation3 permutation2
    _ = mixedMoment B node4191 node4191Labels := by rfl

def raw23531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23531 raw23531Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23531 raw23531Labels = mixedMoment B raw23531step0 raw23531step0Labels := by
      have hz : ∀ j, raw23531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23531step0 = (fun i j => raw23531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23531step0 raw23531; decide +kernel
      have hl : raw23531step0Labels = raw23531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531 raw23531Labels permutation434 hz
    mixedMoment B raw23531step0 raw23531step0Labels = mixedMoment B raw23531step1 raw23531step1Labels := by
      have hz : ∀ j, raw23531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23531step1 = (fun i j => raw23531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23531step1 raw23531step0; decide +kernel
      have hl : raw23531step1Labels = raw23531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23531step0 raw23531step0Labels permutation80 hz
    mixedMoment B raw23531step1 raw23531step1Labels = mixedMoment B raw23531step2 raw23531step2Labels := by
      have ha : raw23531step2 = (fun i j => raw23531step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23531step2 raw23531step1; decide +kernel
      have hl : raw23531step2Labels = raw23531step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23531step1 raw23531step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw23532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23532step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23532 raw23532Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23532 raw23532Labels = mixedMoment B raw23532step0 raw23532step0Labels := by
      have hz : ∀ j, raw23532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23532step0 = (fun i j => raw23532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23532step0 raw23532; decide +kernel
      have hl : raw23532step0Labels = raw23532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23532 raw23532Labels permutation434 hz
    mixedMoment B raw23532step0 raw23532step0Labels = mixedMoment B raw23532step1 raw23532step1Labels := by
      have hz : ∀ j, raw23532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23532step1 = (fun i j => raw23532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23532step1 raw23532step0; decide +kernel
      have hl : raw23532step1Labels = raw23532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23532step0 raw23532step0Labels permutation56 hz
    mixedMoment B raw23532step1 raw23532step1Labels = mixedMoment B raw23532step2 raw23532step2Labels := by
      have ha : raw23532step2 = (fun i j => raw23532step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23532step2 raw23532step1; decide +kernel
      have hl : raw23532step2Labels = raw23532step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23532step1 raw23532step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw23533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw23533step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23533 raw23533Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw23533 raw23533Labels = mixedMoment B raw23533step0 raw23533step0Labels := by
      have hz : ∀ j, raw23533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23533step0 = (fun i j => raw23533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23533step0 raw23533; decide +kernel
      have hl : raw23533step0Labels = raw23533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23533 raw23533Labels permutation346 hz
    mixedMoment B raw23533step0 raw23533step0Labels = mixedMoment B raw23533step1 raw23533step1Labels := by
      have hz : ∀ j, raw23533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23533step1 = (fun i j => raw23533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23533step1 raw23533step0; decide +kernel
      have hl : raw23533step1Labels = raw23533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23533step0 raw23533step0Labels permutation56 hz
    mixedMoment B raw23533step1 raw23533step1Labels = mixedMoment B raw23533step2 raw23533step2Labels := by
      have ha : raw23533step2 = (fun i j => raw23533step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23533step2 raw23533step1; decide +kernel
      have hl : raw23533step2Labels = raw23533step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23533step1 raw23533step1Labels permutation9 permutation2
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw23534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw23534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, -1, -2], ![1, 0, -1]]
def raw23534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23534step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw23534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23534 raw23534Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw23534 raw23534Labels = mixedMoment B raw23534step0 raw23534step0Labels := by
      have hz : ∀ j, raw23534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23534step0 = (fun i j => raw23534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23534step0 raw23534; decide +kernel
      have hl : raw23534step0Labels = raw23534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534 raw23534Labels permutation434 hz
    mixedMoment B raw23534step0 raw23534step0Labels = mixedMoment B raw23534step1 raw23534step1Labels := by
      have hz : ∀ j, raw23534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23534step1 = (fun i j => raw23534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23534step1 raw23534step0; decide +kernel
      have hl : raw23534step1Labels = raw23534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534step0 raw23534step0Labels permutation80 hz
    mixedMoment B raw23534step1 raw23534step1Labels = mixedMoment B raw23534step2 raw23534step2Labels := by
      have hz : ∀ j, raw23534step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23534step2 = (fun i j => raw23534step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23534step2 raw23534step1; decide +kernel
      have hl : raw23534step2Labels = raw23534step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23534step1 raw23534step1Labels permutation14 hz
    mixedMoment B raw23534step2 raw23534step2Labels = mixedMoment B raw23534step3 raw23534step3Labels := by
      have ha : raw23534step3 = (fun i j => raw23534step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23534step3 raw23534step2; decide +kernel
      have hl : raw23534step3Labels = raw23534step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23534step2 raw23534step2Labels permutation3 permutation2
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw23535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23535step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23535step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23535 raw23535Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23535 raw23535Labels = mixedMoment B raw23535step0 raw23535step0Labels := by
      have hz : ∀ j, raw23535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23535step0 = (fun i j => raw23535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23535step0 raw23535; decide +kernel
      have hl : raw23535step0Labels = raw23535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23535 raw23535Labels permutation434 hz
    mixedMoment B raw23535step0 raw23535step0Labels = mixedMoment B raw23535step1 raw23535step1Labels := by
      have hz : ∀ j, raw23535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23535step1 = (fun i j => raw23535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23535step1 raw23535step0; decide +kernel
      have hl : raw23535step1Labels = raw23535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23535step0 raw23535step0Labels permutation80 hz
    mixedMoment B raw23535step1 raw23535step1Labels = mixedMoment B raw23535step2 raw23535step2Labels := by
      have ha : raw23535step2 = (fun i j => raw23535step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23535step2 raw23535step1; decide +kernel
      have hl : raw23535step2Labels = raw23535step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23535step1 raw23535step1Labels permutation9 permutation7
    mixedMoment B raw23535step2 raw23535step2Labels = mixedMoment B raw23535step3 raw23535step3Labels := by
      have ha : raw23535step3 = -raw23535step2 := by apply Matrix.ext; change ∀ i j, raw23535step3 i j = -(raw23535step2 i j); unfold raw23535step3 raw23535step2; decide +kernel
      have hl : raw23535step3Labels = raw23535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23535step3 raw23535step3Labels = mixedMoment B raw23535step4 raw23535step4Labels := by
      have ha : raw23535step4 = raw23535step3 := by apply Matrix.ext; unfold raw23535step4 raw23535step3; decide +kernel
      have hl : raw23535step3Labels = labelEmbedding1 ∘ raw23535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23535step3 raw23535step3Labels raw23535step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw23536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23536step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23536step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23536step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23536 raw23536Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23536 raw23536Labels = mixedMoment B raw23536step0 raw23536step0Labels := by
      have hz : ∀ j, raw23536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23536step0 = (fun i j => raw23536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23536step0 raw23536; decide +kernel
      have hl : raw23536step0Labels = raw23536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536 raw23536Labels permutation434 hz
    mixedMoment B raw23536step0 raw23536step0Labels = mixedMoment B raw23536step1 raw23536step1Labels := by
      have hz : ∀ j, raw23536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23536step1 = (fun i j => raw23536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23536step1 raw23536step0; decide +kernel
      have hl : raw23536step1Labels = raw23536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23536step0 raw23536step0Labels permutation56 hz
    mixedMoment B raw23536step1 raw23536step1Labels = mixedMoment B raw23536step2 raw23536step2Labels := by
      have ha : raw23536step2 = (fun i j => raw23536step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23536step2 raw23536step1; decide +kernel
      have hl : raw23536step2Labels = raw23536step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23536step1 raw23536step1Labels permutation9 permutation7
    mixedMoment B raw23536step2 raw23536step2Labels = mixedMoment B raw23536step3 raw23536step3Labels := by
      have ha : raw23536step3 = -raw23536step2 := by apply Matrix.ext; change ∀ i j, raw23536step3 i j = -(raw23536step2 i j); unfold raw23536step3 raw23536step2; decide +kernel
      have hl : raw23536step3Labels = raw23536step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23536step3 raw23536step3Labels = mixedMoment B raw23536step4 raw23536step4Labels := by
      have ha : raw23536step4 = raw23536step3 := by apply Matrix.ext; unfold raw23536step4 raw23536step3; decide +kernel
      have hl : raw23536step3Labels = labelEmbedding1 ∘ raw23536step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23536step3 raw23536step3Labels raw23536step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw23537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23537step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23537step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23537step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23537 raw23537Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw23537 raw23537Labels = mixedMoment B raw23537step0 raw23537step0Labels := by
      have hz : ∀ j, raw23537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23537step0 = (fun i j => raw23537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23537step0 raw23537; decide +kernel
      have hl : raw23537step0Labels = raw23537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537 raw23537Labels permutation346 hz
    mixedMoment B raw23537step0 raw23537step0Labels = mixedMoment B raw23537step1 raw23537step1Labels := by
      have hz : ∀ j, raw23537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23537step1 = (fun i j => raw23537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23537step1 raw23537step0; decide +kernel
      have hl : raw23537step1Labels = raw23537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23537step0 raw23537step0Labels permutation56 hz
    mixedMoment B raw23537step1 raw23537step1Labels = mixedMoment B raw23537step2 raw23537step2Labels := by
      have ha : raw23537step2 = (fun i j => raw23537step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23537step2 raw23537step1; decide +kernel
      have hl : raw23537step2Labels = raw23537step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23537step1 raw23537step1Labels permutation9 permutation7
    mixedMoment B raw23537step2 raw23537step2Labels = mixedMoment B raw23537step3 raw23537step3Labels := by
      have ha : raw23537step3 = -raw23537step2 := by apply Matrix.ext; change ∀ i j, raw23537step3 i j = -(raw23537step2 i j); unfold raw23537step3 raw23537step2; decide +kernel
      have hl : raw23537step3Labels = raw23537step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23537step3 raw23537step3Labels = mixedMoment B raw23537step4 raw23537step4Labels := by
      have ha : raw23537step4 = raw23537step3 := by apply Matrix.ext; unfold raw23537step4 raw23537step3; decide +kernel
      have hl : raw23537step3Labels = labelEmbedding1 ∘ raw23537step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23537step3 raw23537step3Labels raw23537step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw23538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23538step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 0, -2], ![1, 0, -1]]
def raw23538step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23538step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23538step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23538step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23538step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23538 raw23538Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23538 raw23538Labels = mixedMoment B raw23538step0 raw23538step0Labels := by
      have hz : ∀ j, raw23538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23538step0 = (fun i j => raw23538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23538step0 raw23538; decide +kernel
      have hl : raw23538step0Labels = raw23538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538 raw23538Labels permutation434 hz
    mixedMoment B raw23538step0 raw23538step0Labels = mixedMoment B raw23538step1 raw23538step1Labels := by
      have hz : ∀ j, raw23538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23538step1 = (fun i j => raw23538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23538step1 raw23538step0; decide +kernel
      have hl : raw23538step1Labels = raw23538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step0 raw23538step0Labels permutation80 hz
    mixedMoment B raw23538step1 raw23538step1Labels = mixedMoment B raw23538step2 raw23538step2Labels := by
      have hz : ∀ j, raw23538step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23538step2 = (fun i j => raw23538step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23538step2 raw23538step1; decide +kernel
      have hl : raw23538step2Labels = raw23538step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23538step1 raw23538step1Labels permutation14 hz
    mixedMoment B raw23538step2 raw23538step2Labels = mixedMoment B raw23538step3 raw23538step3Labels := by
      have hz : ∀ i, raw23538step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw23538step3 = (fun i j => raw23538step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw23538step3 raw23538step2; decide +kernel
      have hl : raw23538step3Labels = (fun j => raw23538step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw23538step2 raw23538step2Labels permutation4 hz
    mixedMoment B raw23538step3 raw23538step3Labels = mixedMoment B raw23538step4 raw23538step4Labels := by
      have ha : raw23538step4 = (fun i j => raw23538step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23538step4 raw23538step3; decide +kernel
      have hl : raw23538step4Labels = raw23538step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23538step3 raw23538step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw23539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23539step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23539step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23539step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23539 raw23539Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23539 raw23539Labels = mixedMoment B raw23539step0 raw23539step0Labels := by
      have hz : ∀ j, raw23539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23539step0 = (fun i j => raw23539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23539step0 raw23539; decide +kernel
      have hl : raw23539step0Labels = raw23539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23539 raw23539Labels permutation434 hz
    mixedMoment B raw23539step0 raw23539step0Labels = mixedMoment B raw23539step1 raw23539step1Labels := by
      have hz : ∀ j, raw23539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23539step1 = (fun i j => raw23539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23539step1 raw23539step0; decide +kernel
      have hl : raw23539step1Labels = raw23539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23539step0 raw23539step0Labels permutation80 hz
    mixedMoment B raw23539step1 raw23539step1Labels = mixedMoment B raw23539step2 raw23539step2Labels := by
      have ha : raw23539step2 = (fun i j => raw23539step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23539step2 raw23539step1; decide +kernel
      have hl : raw23539step2Labels = raw23539step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23539step1 raw23539step1Labels permutation9 permutation7
    mixedMoment B raw23539step2 raw23539step2Labels = mixedMoment B raw23539step3 raw23539step3Labels := by
      have ha : raw23539step3 = -raw23539step2 := by apply Matrix.ext; change ∀ i j, raw23539step3 i j = -(raw23539step2 i j); unfold raw23539step3 raw23539step2; decide +kernel
      have hl : raw23539step3Labels = raw23539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23539step3 raw23539step3Labels = mixedMoment B raw23539step4 raw23539step4Labels := by
      have ha : raw23539step4 = raw23539step3 := by apply Matrix.ext; unfold raw23539step4 raw23539step3; decide +kernel
      have hl : raw23539step3Labels = labelEmbedding1 ∘ raw23539step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23539step3 raw23539step3Labels raw23539step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw23540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23540 raw23540Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23540 raw23540Labels = mixedMoment B raw23540step0 raw23540step0Labels := by
      have hz : ∀ j, raw23540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23540step0 = (fun i j => raw23540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23540step0 raw23540; decide +kernel
      have hl : raw23540step0Labels = raw23540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23540 raw23540Labels permutation434 hz
    mixedMoment B raw23540step0 raw23540step0Labels = mixedMoment B raw23540step1 raw23540step1Labels := by
      have ha : raw23540step1 = (fun i j => raw23540step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23540step1 raw23540step0; decide +kernel
      have hl : raw23540step1Labels = raw23540step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23540step0 raw23540step0Labels permutation39 permutation7
    mixedMoment B raw23540step1 raw23540step1Labels = mixedMoment B raw23540step2 raw23540step2Labels := by
      have ha : raw23540step2 = -raw23540step1 := by apply Matrix.ext; change ∀ i j, raw23540step2 i j = -(raw23540step1 i j); unfold raw23540step2 raw23540step1; decide +kernel
      have hl : raw23540step2Labels = raw23540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23540step2 raw23540step2Labels = mixedMoment B raw23540step3 raw23540step3Labels := by
      have ha : raw23540step3 = raw23540step2 := by apply Matrix.ext; unfold raw23540step3 raw23540step2; decide +kernel
      have hl : raw23540step2Labels = labelEmbedding1 ∘ raw23540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23540step2 raw23540step2Labels raw23540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23541 raw23541Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23541 raw23541Labels = mixedMoment B raw23541step0 raw23541step0Labels := by
      have hz : ∀ j, raw23541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23541step0 = (fun i j => raw23541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23541step0 raw23541; decide +kernel
      have hl : raw23541step0Labels = raw23541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23541 raw23541Labels permutation346 hz
    mixedMoment B raw23541step0 raw23541step0Labels = mixedMoment B raw23541step1 raw23541step1Labels := by
      have ha : raw23541step1 = (fun i j => raw23541step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23541step1 raw23541step0; decide +kernel
      have hl : raw23541step1Labels = raw23541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23541step0 raw23541step0Labels permutation39 permutation7
    mixedMoment B raw23541step1 raw23541step1Labels = mixedMoment B raw23541step2 raw23541step2Labels := by
      have ha : raw23541step2 = -raw23541step1 := by apply Matrix.ext; change ∀ i j, raw23541step2 i j = -(raw23541step1 i j); unfold raw23541step2 raw23541step1; decide +kernel
      have hl : raw23541step2Labels = raw23541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23541step2 raw23541step2Labels = mixedMoment B raw23541step3 raw23541step3Labels := by
      have ha : raw23541step3 = raw23541step2 := by apply Matrix.ext; unfold raw23541step3 raw23541step2; decide +kernel
      have hl : raw23541step2Labels = labelEmbedding1 ∘ raw23541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23541step2 raw23541step2Labels raw23541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23542step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23542step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23542step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23542 raw23542Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23542 raw23542Labels = mixedMoment B raw23542step0 raw23542step0Labels := by
      have hz : ∀ j, raw23542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23542step0 = (fun i j => raw23542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23542step0 raw23542; decide +kernel
      have hl : raw23542step0Labels = raw23542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23542 raw23542Labels permutation434 hz
    mixedMoment B raw23542step0 raw23542step0Labels = mixedMoment B raw23542step1 raw23542step1Labels := by
      have hz : ∀ j, raw23542step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23542step1 = (fun i j => raw23542step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23542step1 raw23542step0; decide +kernel
      have hl : raw23542step1Labels = raw23542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23542step0 raw23542step0Labels permutation80 hz
    mixedMoment B raw23542step1 raw23542step1Labels = mixedMoment B raw23542step2 raw23542step2Labels := by
      have ha : raw23542step2 = (fun i j => raw23542step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23542step2 raw23542step1; decide +kernel
      have hl : raw23542step2Labels = raw23542step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23542step1 raw23542step1Labels permutation9 permutation7
    mixedMoment B raw23542step2 raw23542step2Labels = mixedMoment B raw23542step3 raw23542step3Labels := by
      have ha : raw23542step3 = -raw23542step2 := by apply Matrix.ext; change ∀ i j, raw23542step3 i j = -(raw23542step2 i j); unfold raw23542step3 raw23542step2; decide +kernel
      have hl : raw23542step3Labels = raw23542step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23542step3 raw23542step3Labels = mixedMoment B raw23542step4 raw23542step4Labels := by
      have ha : raw23542step4 = raw23542step3 := by apply Matrix.ext; unfold raw23542step4 raw23542step3; decide +kernel
      have hl : raw23542step3Labels = labelEmbedding1 ∘ raw23542step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23542step3 raw23542step3Labels raw23542step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw23543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23543step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23543step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23543step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23543 raw23543Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23543 raw23543Labels = mixedMoment B raw23543step0 raw23543step0Labels := by
      have hz : ∀ j, raw23543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23543step0 = (fun i j => raw23543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23543step0 raw23543; decide +kernel
      have hl : raw23543step0Labels = raw23543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23543 raw23543Labels permutation434 hz
    mixedMoment B raw23543step0 raw23543step0Labels = mixedMoment B raw23543step1 raw23543step1Labels := by
      have hz : ∀ j, raw23543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23543step1 = (fun i j => raw23543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23543step1 raw23543step0; decide +kernel
      have hl : raw23543step1Labels = raw23543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23543step0 raw23543step0Labels permutation56 hz
    mixedMoment B raw23543step1 raw23543step1Labels = mixedMoment B raw23543step2 raw23543step2Labels := by
      have ha : raw23543step2 = (fun i j => raw23543step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23543step2 raw23543step1; decide +kernel
      have hl : raw23543step2Labels = raw23543step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23543step1 raw23543step1Labels permutation9 permutation7
    mixedMoment B raw23543step2 raw23543step2Labels = mixedMoment B raw23543step3 raw23543step3Labels := by
      have ha : raw23543step3 = -raw23543step2 := by apply Matrix.ext; change ∀ i j, raw23543step3 i j = -(raw23543step2 i j); unfold raw23543step3 raw23543step2; decide +kernel
      have hl : raw23543step3Labels = raw23543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23543step3 raw23543step3Labels = mixedMoment B raw23543step4 raw23543step4Labels := by
      have ha : raw23543step4 = raw23543step3 := by apply Matrix.ext; unfold raw23543step4 raw23543step3; decide +kernel
      have hl : raw23543step3Labels = labelEmbedding1 ∘ raw23543step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23543step3 raw23543step3Labels raw23543step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw23544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23544 raw23544Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23544 raw23544Labels = mixedMoment B raw23544step0 raw23544step0Labels := by
      have hz : ∀ j, raw23544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23544step0 = (fun i j => raw23544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23544step0 raw23544; decide +kernel
      have hl : raw23544step0Labels = raw23544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23544 raw23544Labels permutation434 hz
    mixedMoment B raw23544step0 raw23544step0Labels = mixedMoment B raw23544step1 raw23544step1Labels := by
      have ha : raw23544step1 = (fun i j => raw23544step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23544step1 raw23544step0; decide +kernel
      have hl : raw23544step1Labels = raw23544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23544step0 raw23544step0Labels permutation33 permutation7
    mixedMoment B raw23544step1 raw23544step1Labels = mixedMoment B raw23544step2 raw23544step2Labels := by
      have ha : raw23544step2 = -raw23544step1 := by apply Matrix.ext; change ∀ i j, raw23544step2 i j = -(raw23544step1 i j); unfold raw23544step2 raw23544step1; decide +kernel
      have hl : raw23544step2Labels = raw23544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23544step2 raw23544step2Labels = mixedMoment B raw23544step3 raw23544step3Labels := by
      have ha : raw23544step3 = raw23544step2 := by apply Matrix.ext; unfold raw23544step3 raw23544step2; decide +kernel
      have hl : raw23544step2Labels = labelEmbedding1 ∘ raw23544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23544step2 raw23544step2Labels raw23544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23545 raw23545Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23545 raw23545Labels = mixedMoment B raw23545step0 raw23545step0Labels := by
      have hz : ∀ j, raw23545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23545step0 = (fun i j => raw23545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23545step0 raw23545; decide +kernel
      have hl : raw23545step0Labels = raw23545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23545 raw23545Labels permutation265 hz
    mixedMoment B raw23545step0 raw23545step0Labels = mixedMoment B raw23545step1 raw23545step1Labels := by
      have ha : raw23545step1 = (fun i j => raw23545step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23545step1 raw23545step0; decide +kernel
      have hl : raw23545step1Labels = raw23545step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23545step0 raw23545step0Labels permutation39 permutation7
    mixedMoment B raw23545step1 raw23545step1Labels = mixedMoment B raw23545step2 raw23545step2Labels := by
      have ha : raw23545step2 = -raw23545step1 := by apply Matrix.ext; change ∀ i j, raw23545step2 i j = -(raw23545step1 i j); unfold raw23545step2 raw23545step1; decide +kernel
      have hl : raw23545step2Labels = raw23545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23545step2 raw23545step2Labels = mixedMoment B raw23545step3 raw23545step3Labels := by
      have ha : raw23545step3 = raw23545step2 := by apply Matrix.ext; unfold raw23545step3 raw23545step2; decide +kernel
      have hl : raw23545step2Labels = labelEmbedding1 ∘ raw23545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23545step2 raw23545step2Labels raw23545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23546step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23546step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23546step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23546 raw23546Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23546 raw23546Labels = mixedMoment B raw23546step0 raw23546step0Labels := by
      have hz : ∀ j, raw23546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23546step0 = (fun i j => raw23546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23546step0 raw23546; decide +kernel
      have hl : raw23546step0Labels = raw23546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23546 raw23546Labels permutation434 hz
    mixedMoment B raw23546step0 raw23546step0Labels = mixedMoment B raw23546step1 raw23546step1Labels := by
      have hz : ∀ j, raw23546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23546step1 = (fun i j => raw23546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23546step1 raw23546step0; decide +kernel
      have hl : raw23546step1Labels = raw23546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23546step0 raw23546step0Labels permutation56 hz
    mixedMoment B raw23546step1 raw23546step1Labels = mixedMoment B raw23546step2 raw23546step2Labels := by
      have ha : raw23546step2 = (fun i j => raw23546step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23546step2 raw23546step1; decide +kernel
      have hl : raw23546step2Labels = raw23546step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23546step1 raw23546step1Labels permutation9 permutation7
    mixedMoment B raw23546step2 raw23546step2Labels = mixedMoment B raw23546step3 raw23546step3Labels := by
      have ha : raw23546step3 = -raw23546step2 := by apply Matrix.ext; change ∀ i j, raw23546step3 i j = -(raw23546step2 i j); unfold raw23546step3 raw23546step2; decide +kernel
      have hl : raw23546step3Labels = raw23546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23546step3 raw23546step3Labels = mixedMoment B raw23546step4 raw23546step4Labels := by
      have ha : raw23546step4 = raw23546step3 := by apply Matrix.ext; unfold raw23546step4 raw23546step3; decide +kernel
      have hl : raw23546step3Labels = labelEmbedding1 ∘ raw23546step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23546step3 raw23546step3Labels raw23546step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw23547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23547step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23547step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23547step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23547 raw23547Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw23547 raw23547Labels = mixedMoment B raw23547step0 raw23547step0Labels := by
      have hz : ∀ j, raw23547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23547step0 = (fun i j => raw23547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23547step0 raw23547; decide +kernel
      have hl : raw23547step0Labels = raw23547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23547 raw23547Labels permutation346 hz
    mixedMoment B raw23547step0 raw23547step0Labels = mixedMoment B raw23547step1 raw23547step1Labels := by
      have hz : ∀ j, raw23547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23547step1 = (fun i j => raw23547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23547step1 raw23547step0; decide +kernel
      have hl : raw23547step1Labels = raw23547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23547step0 raw23547step0Labels permutation56 hz
    mixedMoment B raw23547step1 raw23547step1Labels = mixedMoment B raw23547step2 raw23547step2Labels := by
      have ha : raw23547step2 = (fun i j => raw23547step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23547step2 raw23547step1; decide +kernel
      have hl : raw23547step2Labels = raw23547step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23547step1 raw23547step1Labels permutation9 permutation7
    mixedMoment B raw23547step2 raw23547step2Labels = mixedMoment B raw23547step3 raw23547step3Labels := by
      have ha : raw23547step3 = -raw23547step2 := by apply Matrix.ext; change ∀ i j, raw23547step3 i j = -(raw23547step2 i j); unfold raw23547step3 raw23547step2; decide +kernel
      have hl : raw23547step3Labels = raw23547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23547step3 raw23547step3Labels = mixedMoment B raw23547step4 raw23547step4Labels := by
      have ha : raw23547step4 = raw23547step3 := by apply Matrix.ext; unfold raw23547step4 raw23547step3; decide +kernel
      have hl : raw23547step3Labels = labelEmbedding1 ∘ raw23547step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23547step3 raw23547step3Labels raw23547step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw23548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23548step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23548step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23548 raw23548Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23548 raw23548Labels = mixedMoment B raw23548step0 raw23548step0Labels := by
      have hz : ∀ j, raw23548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23548step0 = (fun i j => raw23548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23548step0 raw23548; decide +kernel
      have hl : raw23548step0Labels = raw23548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23548 raw23548Labels permutation346 hz
    mixedMoment B raw23548step0 raw23548step0Labels = mixedMoment B raw23548step1 raw23548step1Labels := by
      have ha : raw23548step1 = (fun i j => raw23548step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23548step1 raw23548step0; decide +kernel
      have hl : raw23548step1Labels = raw23548step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23548step0 raw23548step0Labels permutation33 permutation7
    mixedMoment B raw23548step1 raw23548step1Labels = mixedMoment B raw23548step2 raw23548step2Labels := by
      have ha : raw23548step2 = -raw23548step1 := by apply Matrix.ext; change ∀ i j, raw23548step2 i j = -(raw23548step1 i j); unfold raw23548step2 raw23548step1; decide +kernel
      have hl : raw23548step2Labels = raw23548step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23548step2 raw23548step2Labels = mixedMoment B raw23548step3 raw23548step3Labels := by
      have ha : raw23548step3 = raw23548step2 := by apply Matrix.ext; unfold raw23548step3 raw23548step2; decide +kernel
      have hl : raw23548step2Labels = labelEmbedding1 ∘ raw23548step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23548step2 raw23548step2Labels raw23548step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw23549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw23549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw23549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23549 raw23549Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw23549 raw23549Labels = mixedMoment B raw23549step0 raw23549step0Labels := by
      have hz : ∀ j, raw23549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23549step0 = (fun i j => raw23549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23549step0 raw23549; decide +kernel
      have hl : raw23549step0Labels = raw23549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23549 raw23549Labels permutation265 hz
    mixedMoment B raw23549step0 raw23549step0Labels = mixedMoment B raw23549step1 raw23549step1Labels := by
      have ha : raw23549step1 = (fun i j => raw23549step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23549step1 raw23549step0; decide +kernel
      have hl : raw23549step1Labels = raw23549step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23549step0 raw23549step0Labels permutation33 permutation7
    mixedMoment B raw23549step1 raw23549step1Labels = mixedMoment B raw23549step2 raw23549step2Labels := by
      have ha : raw23549step2 = -raw23549step1 := by apply Matrix.ext; change ∀ i j, raw23549step2 i j = -(raw23549step1 i j); unfold raw23549step2 raw23549step1; decide +kernel
      have hl : raw23549step2Labels = raw23549step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23549step2 raw23549step2Labels = mixedMoment B raw23549step3 raw23549step3Labels := by
      have ha : raw23549step3 = raw23549step2 := by apply Matrix.ext; unfold raw23549step3 raw23549step2; decide +kernel
      have hl : raw23549step2Labels = labelEmbedding1 ∘ raw23549step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23549step2 raw23549step2Labels raw23549step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw23550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw23550step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23550 raw23550Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw23550 raw23550Labels = mixedMoment B raw23550step0 raw23550step0Labels := by
      have hz : ∀ j, raw23550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23550step0 = (fun i j => raw23550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23550step0 raw23550; decide +kernel
      have hl : raw23550step0Labels = raw23550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23550 raw23550Labels permutation346 hz
    mixedMoment B raw23550step0 raw23550step0Labels = mixedMoment B raw23550step1 raw23550step1Labels := by
      have hz : ∀ j, raw23550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23550step1 = (fun i j => raw23550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23550step1 raw23550step0; decide +kernel
      have hl : raw23550step1Labels = raw23550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23550step0 raw23550step0Labels permutation56 hz
    mixedMoment B raw23550step1 raw23550step1Labels = mixedMoment B raw23550step2 raw23550step2Labels := by
      have ha : raw23550step2 = (fun i j => raw23550step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23550step2 raw23550step1; decide +kernel
      have hl : raw23550step2Labels = raw23550step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23550step1 raw23550step1Labels permutation9 permutation7
    mixedMoment B raw23550step2 raw23550step2Labels = mixedMoment B raw23550step3 raw23550step3Labels := by
      have ha : raw23550step3 = -raw23550step2 := by apply Matrix.ext; change ∀ i j, raw23550step3 i j = -(raw23550step2 i j); unfold raw23550step3 raw23550step2; decide +kernel
      have hl : raw23550step3Labels = raw23550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23550step3 raw23550step3Labels = mixedMoment B raw23550step4 raw23550step4Labels := by
      have ha : raw23550step4 = raw23550step3 := by apply Matrix.ext; unfold raw23550step4 raw23550step3; decide +kernel
      have hl : raw23550step3Labels = labelEmbedding1 ∘ raw23550step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23550step3 raw23550step3Labels raw23550step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw23551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw23551step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, -1, -2], ![2, -1, -1]]
def raw23551step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw23551step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23551step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw23551step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23551 raw23551Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw23551 raw23551Labels = mixedMoment B raw23551step0 raw23551step0Labels := by
      have hz : ∀ j, raw23551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23551step0 = (fun i j => raw23551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23551step0 raw23551; decide +kernel
      have hl : raw23551step0Labels = raw23551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551 raw23551Labels permutation434 hz
    mixedMoment B raw23551step0 raw23551step0Labels = mixedMoment B raw23551step1 raw23551step1Labels := by
      have hz : ∀ j, raw23551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23551step1 = (fun i j => raw23551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23551step1 raw23551step0; decide +kernel
      have hl : raw23551step1Labels = raw23551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551step0 raw23551step0Labels permutation80 hz
    mixedMoment B raw23551step1 raw23551step1Labels = mixedMoment B raw23551step2 raw23551step2Labels := by
      have hz : ∀ j, raw23551step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23551step2 = (fun i j => raw23551step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23551step2 raw23551step1; decide +kernel
      have hl : raw23551step2Labels = raw23551step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23551step1 raw23551step1Labels permutation14 hz
    mixedMoment B raw23551step2 raw23551step2Labels = mixedMoment B raw23551step3 raw23551step3Labels := by
      have ha : raw23551step3 = (fun i j => raw23551step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23551step3 raw23551step2; decide +kernel
      have hl : raw23551step3Labels = raw23551step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23551step2 raw23551step2Labels permutation3 permutation7
    mixedMoment B raw23551step3 raw23551step3Labels = mixedMoment B raw23551step4 raw23551step4Labels := by
      have ha : raw23551step4 = -raw23551step3 := by apply Matrix.ext; change ∀ i j, raw23551step4 i j = -(raw23551step3 i j); unfold raw23551step4 raw23551step3; decide +kernel
      have hl : raw23551step4Labels = raw23551step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23551step4 raw23551step4Labels = mixedMoment B raw23551step5 raw23551step5Labels := by
      have ha : raw23551step5 = raw23551step4 := by apply Matrix.ext; unfold raw23551step5 raw23551step4; decide +kernel
      have hl : raw23551step4Labels = labelEmbedding1 ∘ raw23551step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23551step4 raw23551step4Labels raw23551step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
