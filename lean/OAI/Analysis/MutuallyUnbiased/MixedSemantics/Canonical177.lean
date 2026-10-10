import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22656step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22656 raw22656Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw22656 raw22656Labels = mixedMoment B raw22656step0 raw22656step0Labels := by
      have hz : ∀ j, raw22656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22656step0 = (fun i j => raw22656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22656step0 raw22656; decide +kernel
      have hl : raw22656step0Labels = raw22656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22656 raw22656Labels permutation346 hz
    mixedMoment B raw22656step0 raw22656step0Labels = mixedMoment B raw22656step1 raw22656step1Labels := by
      have ha : raw22656step1 = (fun i j => raw22656step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22656step1 raw22656step0; decide +kernel
      have hl : raw22656step1Labels = raw22656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22656step0 raw22656step0Labels permutation38 permutation3
    mixedMoment B raw22656step1 raw22656step1Labels = mixedMoment B raw22656step2 raw22656step2Labels := by
      have ha : raw22656step2 = raw22656step1 := by apply Matrix.ext; unfold raw22656step2 raw22656step1; decide +kernel
      have hl : raw22656step1Labels = labelEmbedding6 ∘ raw22656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22656step1 raw22656step1Labels raw22656step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw22657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22657step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22657 raw22657Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw22657 raw22657Labels = mixedMoment B raw22657step0 raw22657step0Labels := by
      have ha : raw22657step0 = (fun i j => raw22657 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22657step0 raw22657; decide +kernel
      have hl : raw22657step0Labels = raw22657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22657 raw22657Labels permutation182 permutation3
    mixedMoment B raw22657step0 raw22657step0Labels = mixedMoment B raw22657step1 raw22657step1Labels := by
      have ha : raw22657step1 = raw22657step0 := by apply Matrix.ext; unfold raw22657step1 raw22657step0; decide +kernel
      have hl : raw22657step0Labels = labelEmbedding6 ∘ raw22657step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22657step0 raw22657step0Labels raw22657step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw22658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22658 raw22658Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22658 raw22658Labels = mixedMoment B raw22658step0 raw22658step0Labels := by
      have hz : ∀ j, raw22658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22658step0 = (fun i j => raw22658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22658step0 raw22658; decide +kernel
      have hl : raw22658step0Labels = raw22658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22658 raw22658Labels permutation346 hz
    mixedMoment B raw22658step0 raw22658step0Labels = mixedMoment B raw22658step1 raw22658step1Labels := by
      have ha : raw22658step1 = (fun i j => raw22658step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22658step1 raw22658step0; decide +kernel
      have hl : raw22658step1Labels = raw22658step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22658step0 raw22658step0Labels permutation39 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw22659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22659 raw22659Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22659 raw22659Labels = mixedMoment B raw22659step0 raw22659step0Labels := by
      have hz : ∀ j, raw22659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22659step0 = (fun i j => raw22659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22659step0 raw22659; decide +kernel
      have hl : raw22659step0Labels = raw22659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22659 raw22659Labels permutation346 hz
    mixedMoment B raw22659step0 raw22659step0Labels = mixedMoment B raw22659step1 raw22659step1Labels := by
      have ha : raw22659step1 = (fun i j => raw22659step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22659step1 raw22659step0; decide +kernel
      have hl : raw22659step1Labels = raw22659step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22659step0 raw22659step0Labels permutation39 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw22660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22660 raw22660Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw22660 raw22660Labels = mixedMoment B raw22660step0 raw22660step0Labels := by
      have hz : ∀ j, raw22660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22660step0 = (fun i j => raw22660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22660step0 raw22660; decide +kernel
      have hl : raw22660step0Labels = raw22660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22660 raw22660Labels permutation265 hz
    mixedMoment B raw22660step0 raw22660step0Labels = mixedMoment B raw22660step1 raw22660step1Labels := by
      have ha : raw22660step1 = (fun i j => raw22660step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22660step1 raw22660step0; decide +kernel
      have hl : raw22660step1Labels = raw22660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22660step0 raw22660step0Labels permutation38 permutation3
    mixedMoment B raw22660step1 raw22660step1Labels = mixedMoment B raw22660step2 raw22660step2Labels := by
      have ha : raw22660step2 = raw22660step1 := by apply Matrix.ext; unfold raw22660step2 raw22660step1; decide +kernel
      have hl : raw22660step1Labels = labelEmbedding6 ∘ raw22660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22660step1 raw22660step1Labels raw22660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw22661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22661step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22661 raw22661Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw22661 raw22661Labels = mixedMoment B raw22661step0 raw22661step0Labels := by
      have ha : raw22661step0 = (fun i j => raw22661 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22661step0 raw22661; decide +kernel
      have hl : raw22661step0Labels = raw22661Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22661 raw22661Labels permutation158 permutation3
    mixedMoment B raw22661step0 raw22661step0Labels = mixedMoment B raw22661step1 raw22661step1Labels := by
      have ha : raw22661step1 = raw22661step0 := by apply Matrix.ext; unfold raw22661step1 raw22661step0; decide +kernel
      have hl : raw22661step0Labels = labelEmbedding6 ∘ raw22661step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22661step0 raw22661step0Labels raw22661step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw22662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22662 raw22662Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22662 raw22662Labels = mixedMoment B raw22662step0 raw22662step0Labels := by
      have hz : ∀ j, raw22662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22662step0 = (fun i j => raw22662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22662step0 raw22662; decide +kernel
      have hl : raw22662step0Labels = raw22662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22662 raw22662Labels permutation265 hz
    mixedMoment B raw22662step0 raw22662step0Labels = mixedMoment B raw22662step1 raw22662step1Labels := by
      have ha : raw22662step1 = (fun i j => raw22662step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22662step1 raw22662step0; decide +kernel
      have hl : raw22662step1Labels = raw22662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22662step0 raw22662step0Labels permutation39 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw22663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22663 raw22663Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22663 raw22663Labels = mixedMoment B raw22663step0 raw22663step0Labels := by
      have hz : ∀ j, raw22663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22663step0 = (fun i j => raw22663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22663step0 raw22663; decide +kernel
      have hl : raw22663step0Labels = raw22663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22663 raw22663Labels permutation265 hz
    mixedMoment B raw22663step0 raw22663step0Labels = mixedMoment B raw22663step1 raw22663step1Labels := by
      have ha : raw22663step1 = (fun i j => raw22663step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22663step1 raw22663step0; decide +kernel
      have hl : raw22663step1Labels = raw22663step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22663step0 raw22663step0Labels permutation39 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw22664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22664step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22664 raw22664Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw22664 raw22664Labels = mixedMoment B raw22664step0 raw22664step0Labels := by
      have hz : ∀ j, raw22664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22664step0 = (fun i j => raw22664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22664step0 raw22664; decide +kernel
      have hl : raw22664step0Labels = raw22664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22664 raw22664Labels permutation346 hz
    mixedMoment B raw22664step0 raw22664step0Labels = mixedMoment B raw22664step1 raw22664step1Labels := by
      have hz : ∀ j, raw22664step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22664step1 = (fun i j => raw22664step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22664step1 raw22664step0; decide +kernel
      have hl : raw22664step1Labels = raw22664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22664step0 raw22664step0Labels permutation56 hz
    mixedMoment B raw22664step1 raw22664step1Labels = mixedMoment B raw22664step2 raw22664step2Labels := by
      have ha : raw22664step2 = (fun i j => raw22664step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22664step2 raw22664step1; decide +kernel
      have hl : raw22664step2Labels = raw22664step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22664step1 raw22664step1Labels permutation8 permutation3
    mixedMoment B raw22664step2 raw22664step2Labels = mixedMoment B raw22664step3 raw22664step3Labels := by
      have ha : raw22664step3 = raw22664step2 := by apply Matrix.ext; unfold raw22664step3 raw22664step2; decide +kernel
      have hl : raw22664step2Labels = labelEmbedding6 ∘ raw22664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22664step2 raw22664step2Labels raw22664step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4188 node4188Labels := by rfl

def raw22665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22665 raw22665Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw22665 raw22665Labels = mixedMoment B raw22665step0 raw22665step0Labels := by
      have hz : ∀ j, raw22665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22665step0 = (fun i j => raw22665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22665step0 raw22665; decide +kernel
      have hl : raw22665step0Labels = raw22665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22665 raw22665Labels permutation346 hz
    mixedMoment B raw22665step0 raw22665step0Labels = mixedMoment B raw22665step1 raw22665step1Labels := by
      have ha : raw22665step1 = (fun i j => raw22665step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22665step1 raw22665step0; decide +kernel
      have hl : raw22665step1Labels = raw22665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22665step0 raw22665step0Labels permutation32 permutation3
    mixedMoment B raw22665step1 raw22665step1Labels = mixedMoment B raw22665step2 raw22665step2Labels := by
      have ha : raw22665step2 = raw22665step1 := by apply Matrix.ext; unfold raw22665step2 raw22665step1; decide +kernel
      have hl : raw22665step1Labels = labelEmbedding6 ∘ raw22665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22665step1 raw22665step1Labels raw22665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

def raw22666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22666step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22666 raw22666Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw22666 raw22666Labels = mixedMoment B raw22666step0 raw22666step0Labels := by
      have hz : ∀ j, raw22666 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22666step0 = (fun i j => raw22666 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22666step0 raw22666; decide +kernel
      have hl : raw22666step0Labels = raw22666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22666 raw22666Labels permutation265 hz
    mixedMoment B raw22666step0 raw22666step0Labels = mixedMoment B raw22666step1 raw22666step1Labels := by
      have ha : raw22666step1 = (fun i j => raw22666step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22666step1 raw22666step0; decide +kernel
      have hl : raw22666step1Labels = raw22666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22666step0 raw22666step0Labels permutation32 permutation3
    mixedMoment B raw22666step1 raw22666step1Labels = mixedMoment B raw22666step2 raw22666step2Labels := by
      have ha : raw22666step2 = raw22666step1 := by apply Matrix.ext; unfold raw22666step2 raw22666step1; decide +kernel
      have hl : raw22666step1Labels = labelEmbedding6 ∘ raw22666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22666step1 raw22666step1Labels raw22666step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

def raw22667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22667 raw22667Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw22667 raw22667Labels = mixedMoment B raw22667step0 raw22667step0Labels := by
      have hz : ∀ j, raw22667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22667step0 = (fun i j => raw22667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22667step0 raw22667; decide +kernel
      have hl : raw22667step0Labels = raw22667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22667 raw22667Labels permutation346 hz
    mixedMoment B raw22667step0 raw22667step0Labels = mixedMoment B raw22667step1 raw22667step1Labels := by
      have hz : ∀ j, raw22667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22667step1 = (fun i j => raw22667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22667step1 raw22667step0; decide +kernel
      have hl : raw22667step1Labels = raw22667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22667step0 raw22667step0Labels permutation56 hz
    mixedMoment B raw22667step1 raw22667step1Labels = mixedMoment B raw22667step2 raw22667step2Labels := by
      have ha : raw22667step2 = (fun i j => raw22667step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22667step2 raw22667step1; decide +kernel
      have hl : raw22667step2Labels = raw22667step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22667step1 raw22667step1Labels permutation9 permutation2
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw22668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22668 raw22668Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw22668 raw22668Labels = mixedMoment B raw22668step0 raw22668step0Labels := by
      have hz : ∀ j, raw22668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22668step0 = (fun i j => raw22668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22668step0 raw22668; decide +kernel
      have hl : raw22668step0Labels = raw22668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22668 raw22668Labels permutation346 hz
    mixedMoment B raw22668step0 raw22668step0Labels = mixedMoment B raw22668step1 raw22668step1Labels := by
      have hz : ∀ j, raw22668step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22668step1 = (fun i j => raw22668step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22668step1 raw22668step0; decide +kernel
      have hl : raw22668step1Labels = raw22668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22668step0 raw22668step0Labels permutation56 hz
    mixedMoment B raw22668step1 raw22668step1Labels = mixedMoment B raw22668step2 raw22668step2Labels := by
      have ha : raw22668step2 = (fun i j => raw22668step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22668step2 raw22668step1; decide +kernel
      have hl : raw22668step2Labels = raw22668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22668step1 raw22668step1Labels permutation9 permutation3
    mixedMoment B raw22668step2 raw22668step2Labels = mixedMoment B raw22668step3 raw22668step3Labels := by
      have ha : raw22668step3 = raw22668step2 := by apply Matrix.ext; unfold raw22668step3 raw22668step2; decide +kernel
      have hl : raw22668step2Labels = labelEmbedding6 ∘ raw22668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22668step2 raw22668step2Labels raw22668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw22669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22669 raw22669Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw22669 raw22669Labels = mixedMoment B raw22669step0 raw22669step0Labels := by
      have hz : ∀ j, raw22669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22669step0 = (fun i j => raw22669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22669step0 raw22669; decide +kernel
      have hl : raw22669step0Labels = raw22669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22669 raw22669Labels permutation346 hz
    mixedMoment B raw22669step0 raw22669step0Labels = mixedMoment B raw22669step1 raw22669step1Labels := by
      have ha : raw22669step1 = (fun i j => raw22669step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22669step1 raw22669step0; decide +kernel
      have hl : raw22669step1Labels = raw22669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22669step0 raw22669step0Labels permutation33 permutation3
    mixedMoment B raw22669step1 raw22669step1Labels = mixedMoment B raw22669step2 raw22669step2Labels := by
      have ha : raw22669step2 = raw22669step1 := by apply Matrix.ext; unfold raw22669step2 raw22669step1; decide +kernel
      have hl : raw22669step1Labels = labelEmbedding6 ∘ raw22669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22669step1 raw22669step1Labels raw22669step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw22670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22670 raw22670Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw22670 raw22670Labels = mixedMoment B raw22670step0 raw22670step0Labels := by
      have hz : ∀ j, raw22670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22670step0 = (fun i j => raw22670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22670step0 raw22670; decide +kernel
      have hl : raw22670step0Labels = raw22670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22670 raw22670Labels permutation265 hz
    mixedMoment B raw22670step0 raw22670step0Labels = mixedMoment B raw22670step1 raw22670step1Labels := by
      have ha : raw22670step1 = (fun i j => raw22670step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22670step1 raw22670step0; decide +kernel
      have hl : raw22670step1Labels = raw22670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22670step0 raw22670step0Labels permutation33 permutation3
    mixedMoment B raw22670step1 raw22670step1Labels = mixedMoment B raw22670step2 raw22670step2Labels := by
      have ha : raw22670step2 = raw22670step1 := by apply Matrix.ext; unfold raw22670step2 raw22670step1; decide +kernel
      have hl : raw22670step1Labels = labelEmbedding6 ∘ raw22670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22670step1 raw22670step1Labels raw22670step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw22671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22671step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22671 raw22671Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw22671 raw22671Labels = mixedMoment B raw22671step0 raw22671step0Labels := by
      have hz : ∀ j, raw22671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22671step0 = (fun i j => raw22671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22671step0 raw22671; decide +kernel
      have hl : raw22671step0Labels = raw22671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22671 raw22671Labels permutation346 hz
    mixedMoment B raw22671step0 raw22671step0Labels = mixedMoment B raw22671step1 raw22671step1Labels := by
      have hz : ∀ j, raw22671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22671step1 = (fun i j => raw22671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22671step1 raw22671step0; decide +kernel
      have hl : raw22671step1Labels = raw22671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22671step0 raw22671step0Labels permutation56 hz
    mixedMoment B raw22671step1 raw22671step1Labels = mixedMoment B raw22671step2 raw22671step2Labels := by
      have ha : raw22671step2 = (fun i j => raw22671step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22671step2 raw22671step1; decide +kernel
      have hl : raw22671step2Labels = raw22671step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22671step1 raw22671step1Labels permutation9 permutation2
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw22672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw22672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22672 raw22672Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw22672 raw22672Labels = mixedMoment B raw22672step0 raw22672step0Labels := by
      have hz : ∀ j, raw22672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22672step0 = (fun i j => raw22672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22672step0 raw22672; decide +kernel
      have hl : raw22672step0Labels = raw22672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22672 raw22672Labels permutation346 hz
    mixedMoment B raw22672step0 raw22672step0Labels = mixedMoment B raw22672step1 raw22672step1Labels := by
      have hz : ∀ j, raw22672step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22672step1 = (fun i j => raw22672step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22672step1 raw22672step0; decide +kernel
      have hl : raw22672step1Labels = raw22672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22672step0 raw22672step0Labels permutation56 hz
    mixedMoment B raw22672step1 raw22672step1Labels = mixedMoment B raw22672step2 raw22672step2Labels := by
      have ha : raw22672step2 = (fun i j => raw22672step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22672step2 raw22672step1; decide +kernel
      have hl : raw22672step2Labels = raw22672step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22672step1 raw22672step1Labels permutation9 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw22673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22673 raw22673Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw22673 raw22673Labels = mixedMoment B raw22673step0 raw22673step0Labels := by
      have hz : ∀ j, raw22673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22673step0 = (fun i j => raw22673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22673step0 raw22673; decide +kernel
      have hl : raw22673step0Labels = raw22673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22673 raw22673Labels permutation346 hz
    mixedMoment B raw22673step0 raw22673step0Labels = mixedMoment B raw22673step1 raw22673step1Labels := by
      have hz : ∀ j, raw22673step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22673step1 = (fun i j => raw22673step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22673step1 raw22673step0; decide +kernel
      have hl : raw22673step1Labels = raw22673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22673step0 raw22673step0Labels permutation56 hz
    mixedMoment B raw22673step1 raw22673step1Labels = mixedMoment B raw22673step2 raw22673step2Labels := by
      have ha : raw22673step2 = (fun i j => raw22673step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22673step2 raw22673step1; decide +kernel
      have hl : raw22673step2Labels = raw22673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22673step1 raw22673step1Labels permutation8 permutation3
    mixedMoment B raw22673step2 raw22673step2Labels = mixedMoment B raw22673step3 raw22673step3Labels := by
      have ha : raw22673step3 = raw22673step2 := by apply Matrix.ext; unfold raw22673step3 raw22673step2; decide +kernel
      have hl : raw22673step2Labels = labelEmbedding6 ∘ raw22673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22673step2 raw22673step2Labels raw22673step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4160 node4160Labels := by rfl

def raw22674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22674 raw22674Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw22674 raw22674Labels = mixedMoment B raw22674step0 raw22674step0Labels := by
      have hz : ∀ j, raw22674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22674step0 = (fun i j => raw22674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22674step0 raw22674; decide +kernel
      have hl : raw22674step0Labels = raw22674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22674 raw22674Labels permutation346 hz
    mixedMoment B raw22674step0 raw22674step0Labels = mixedMoment B raw22674step1 raw22674step1Labels := by
      have ha : raw22674step1 = (fun i j => raw22674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22674step1 raw22674step0; decide +kernel
      have hl : raw22674step1Labels = raw22674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22674step0 raw22674step0Labels permutation32 permutation3
    mixedMoment B raw22674step1 raw22674step1Labels = mixedMoment B raw22674step2 raw22674step2Labels := by
      have ha : raw22674step2 = raw22674step1 := by apply Matrix.ext; unfold raw22674step2 raw22674step1; decide +kernel
      have hl : raw22674step1Labels = labelEmbedding6 ∘ raw22674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22674step1 raw22674step1Labels raw22674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw22675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22675 raw22675Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw22675 raw22675Labels = mixedMoment B raw22675step0 raw22675step0Labels := by
      have hz : ∀ j, raw22675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22675step0 = (fun i j => raw22675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22675step0 raw22675; decide +kernel
      have hl : raw22675step0Labels = raw22675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22675 raw22675Labels permutation265 hz
    mixedMoment B raw22675step0 raw22675step0Labels = mixedMoment B raw22675step1 raw22675step1Labels := by
      have ha : raw22675step1 = (fun i j => raw22675step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22675step1 raw22675step0; decide +kernel
      have hl : raw22675step1Labels = raw22675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22675step0 raw22675step0Labels permutation32 permutation3
    mixedMoment B raw22675step1 raw22675step1Labels = mixedMoment B raw22675step2 raw22675step2Labels := by
      have ha : raw22675step2 = raw22675step1 := by apply Matrix.ext; unfold raw22675step2 raw22675step1; decide +kernel
      have hl : raw22675step1Labels = labelEmbedding6 ∘ raw22675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22675step1 raw22675step1Labels raw22675step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw22676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22676 raw22676Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw22676 raw22676Labels = mixedMoment B raw22676step0 raw22676step0Labels := by
      have hz : ∀ j, raw22676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22676step0 = (fun i j => raw22676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22676step0 raw22676; decide +kernel
      have hl : raw22676step0Labels = raw22676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22676 raw22676Labels permutation346 hz
    mixedMoment B raw22676step0 raw22676step0Labels = mixedMoment B raw22676step1 raw22676step1Labels := by
      have hz : ∀ j, raw22676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22676step1 = (fun i j => raw22676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22676step1 raw22676step0; decide +kernel
      have hl : raw22676step1Labels = raw22676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22676step0 raw22676step0Labels permutation56 hz
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw22677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22677step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw22677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22677 raw22677Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw22677 raw22677Labels = mixedMoment B raw22677step0 raw22677step0Labels := by
      have hz : ∀ j, raw22677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22677step0 = (fun i j => raw22677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22677step0 raw22677; decide +kernel
      have hl : raw22677step0Labels = raw22677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22677 raw22677Labels permutation346 hz
    mixedMoment B raw22677step0 raw22677step0Labels = mixedMoment B raw22677step1 raw22677step1Labels := by
      have hz : ∀ j, raw22677step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22677step1 = (fun i j => raw22677step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22677step1 raw22677step0; decide +kernel
      have hl : raw22677step1Labels = raw22677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22677step0 raw22677step0Labels permutation56 hz
    mixedMoment B raw22677step1 raw22677step1Labels = mixedMoment B raw22677step2 raw22677step2Labels := by
      have ha : raw22677step2 = (fun i j => raw22677step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22677step2 raw22677step1; decide +kernel
      have hl : raw22677step2Labels = raw22677step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22677step1 raw22677step1Labels permutation8 permutation3
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw22678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22678 raw22678Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw22678 raw22678Labels = mixedMoment B raw22678step0 raw22678step0Labels := by
      have hz : ∀ j, raw22678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22678step0 = (fun i j => raw22678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22678step0 raw22678; decide +kernel
      have hl : raw22678step0Labels = raw22678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22678 raw22678Labels permutation346 hz
    mixedMoment B raw22678step0 raw22678step0Labels = mixedMoment B raw22678step1 raw22678step1Labels := by
      have ha : raw22678step1 = (fun i j => raw22678step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22678step1 raw22678step0; decide +kernel
      have hl : raw22678step1Labels = raw22678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22678step0 raw22678step0Labels permutation38 permutation3
    _ = mixedMoment B node586 node586Labels := by rfl

def raw22679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22679 raw22679Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw22679 raw22679Labels = mixedMoment B raw22679step0 raw22679step0Labels := by
      have ha : raw22679step0 = (fun i j => raw22679 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22679step0 raw22679; decide +kernel
      have hl : raw22679step0Labels = raw22679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22679 raw22679Labels permutation182 permutation3
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw22680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22680 raw22680Labels = mixedMoment B node1172 node1172Labels := by
  calc
    mixedMoment B raw22680 raw22680Labels = mixedMoment B raw22680step0 raw22680step0Labels := by
      have hz : ∀ j, raw22680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22680step0 = (fun i j => raw22680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22680step0 raw22680; decide +kernel
      have hl : raw22680step0Labels = raw22680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22680 raw22680Labels permutation346 hz
    mixedMoment B raw22680step0 raw22680step0Labels = mixedMoment B raw22680step1 raw22680step1Labels := by
      have ha : raw22680step1 = (fun i j => raw22680step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22680step1 raw22680step0; decide +kernel
      have hl : raw22680step1Labels = raw22680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22680step0 raw22680step0Labels permutation38 permutation3
    _ = mixedMoment B node1172 node1172Labels := by rfl

def raw22681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22681 raw22681Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw22681 raw22681Labels = mixedMoment B raw22681step0 raw22681step0Labels := by
      have hz : ∀ j, raw22681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22681step0 = (fun i j => raw22681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22681step0 raw22681; decide +kernel
      have hl : raw22681step0Labels = raw22681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22681 raw22681Labels permutation346 hz
    mixedMoment B raw22681step0 raw22681step0Labels = mixedMoment B raw22681step1 raw22681step1Labels := by
      have ha : raw22681step1 = (fun i j => raw22681step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22681step1 raw22681step0; decide +kernel
      have hl : raw22681step1Labels = raw22681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22681step0 raw22681step0Labels permutation42 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw22682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22682 raw22682Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw22682 raw22682Labels = mixedMoment B raw22682step0 raw22682step0Labels := by
      have hz : ∀ j, raw22682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22682step0 = (fun i j => raw22682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22682step0 raw22682; decide +kernel
      have hl : raw22682step0Labels = raw22682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22682 raw22682Labels permutation265 hz
    mixedMoment B raw22682step0 raw22682step0Labels = mixedMoment B raw22682step1 raw22682step1Labels := by
      have ha : raw22682step1 = (fun i j => raw22682step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22682step1 raw22682step0; decide +kernel
      have hl : raw22682step1Labels = raw22682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22682step0 raw22682step0Labels permutation38 permutation3
    _ = mixedMoment B node586 node586Labels := by rfl

def raw22683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22683 raw22683Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw22683 raw22683Labels = mixedMoment B raw22683step0 raw22683step0Labels := by
      have ha : raw22683step0 = (fun i j => raw22683 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22683step0 raw22683; decide +kernel
      have hl : raw22683step0Labels = raw22683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22683 raw22683Labels permutation158 permutation3
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw22684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22684 raw22684Labels = mixedMoment B node1172 node1172Labels := by
  calc
    mixedMoment B raw22684 raw22684Labels = mixedMoment B raw22684step0 raw22684step0Labels := by
      have hz : ∀ j, raw22684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22684step0 = (fun i j => raw22684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22684step0 raw22684; decide +kernel
      have hl : raw22684step0Labels = raw22684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22684 raw22684Labels permutation265 hz
    mixedMoment B raw22684step0 raw22684step0Labels = mixedMoment B raw22684step1 raw22684step1Labels := by
      have ha : raw22684step1 = (fun i j => raw22684step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22684step1 raw22684step0; decide +kernel
      have hl : raw22684step1Labels = raw22684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22684step0 raw22684step0Labels permutation38 permutation3
    _ = mixedMoment B node1172 node1172Labels := by rfl

def raw22685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22685 raw22685Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw22685 raw22685Labels = mixedMoment B raw22685step0 raw22685step0Labels := by
      have hz : ∀ j, raw22685 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22685step0 = (fun i j => raw22685 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22685step0 raw22685; decide +kernel
      have hl : raw22685step0Labels = raw22685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22685 raw22685Labels permutation265 hz
    mixedMoment B raw22685step0 raw22685step0Labels = mixedMoment B raw22685step1 raw22685step1Labels := by
      have ha : raw22685step1 = (fun i j => raw22685step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22685step1 raw22685step0; decide +kernel
      have hl : raw22685step1Labels = raw22685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22685step0 raw22685step0Labels permutation42 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw22686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22686 raw22686Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw22686 raw22686Labels = mixedMoment B raw22686step0 raw22686step0Labels := by
      have hz : ∀ j, raw22686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22686step0 = (fun i j => raw22686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22686step0 raw22686; decide +kernel
      have hl : raw22686step0Labels = raw22686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22686 raw22686Labels permutation346 hz
    mixedMoment B raw22686step0 raw22686step0Labels = mixedMoment B raw22686step1 raw22686step1Labels := by
      have hz : ∀ j, raw22686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22686step1 = (fun i j => raw22686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22686step1 raw22686step0; decide +kernel
      have hl : raw22686step1Labels = raw22686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22686step0 raw22686step0Labels permutation56 hz
    mixedMoment B raw22686step1 raw22686step1Labels = mixedMoment B raw22686step2 raw22686step2Labels := by
      have ha : raw22686step2 = (fun i j => raw22686step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22686step2 raw22686step1; decide +kernel
      have hl : raw22686step2Labels = raw22686step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22686step1 raw22686step1Labels permutation8 permutation3
    _ = mixedMoment B node616 node616Labels := by rfl

def raw22687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22687 raw22687Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw22687 raw22687Labels = mixedMoment B raw22687step0 raw22687step0Labels := by
      have hz : ∀ j, raw22687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22687step0 = (fun i j => raw22687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22687step0 raw22687; decide +kernel
      have hl : raw22687step0Labels = raw22687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22687 raw22687Labels permutation346 hz
    mixedMoment B raw22687step0 raw22687step0Labels = mixedMoment B raw22687step1 raw22687step1Labels := by
      have ha : raw22687step1 = (fun i j => raw22687step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22687step1 raw22687step0; decide +kernel
      have hl : raw22687step1Labels = raw22687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22687step0 raw22687step0Labels permutation32 permutation3
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw22688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22688 raw22688Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw22688 raw22688Labels = mixedMoment B raw22688step0 raw22688step0Labels := by
      have hz : ∀ j, raw22688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22688step0 = (fun i j => raw22688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22688step0 raw22688; decide +kernel
      have hl : raw22688step0Labels = raw22688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22688 raw22688Labels permutation265 hz
    mixedMoment B raw22688step0 raw22688step0Labels = mixedMoment B raw22688step1 raw22688step1Labels := by
      have ha : raw22688step1 = (fun i j => raw22688step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22688step1 raw22688step0; decide +kernel
      have hl : raw22688step1Labels = raw22688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22688step0 raw22688step0Labels permutation32 permutation3
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw22689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22689step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22689 raw22689Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw22689 raw22689Labels = mixedMoment B raw22689step0 raw22689step0Labels := by
      have hz : ∀ j, raw22689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22689step0 = (fun i j => raw22689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22689step0 raw22689; decide +kernel
      have hl : raw22689step0Labels = raw22689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22689 raw22689Labels permutation346 hz
    mixedMoment B raw22689step0 raw22689step0Labels = mixedMoment B raw22689step1 raw22689step1Labels := by
      have hz : ∀ j, raw22689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22689step1 = (fun i j => raw22689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22689step1 raw22689step0; decide +kernel
      have hl : raw22689step1Labels = raw22689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22689step0 raw22689step0Labels permutation56 hz
    mixedMoment B raw22689step1 raw22689step1Labels = mixedMoment B raw22689step2 raw22689step2Labels := by
      have ha : raw22689step2 = (fun i j => raw22689step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22689step2 raw22689step1; decide +kernel
      have hl : raw22689step2Labels = raw22689step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22689step1 raw22689step1Labels permutation12 permutation3
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw22690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22690 raw22690Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw22690 raw22690Labels = mixedMoment B raw22690step0 raw22690step0Labels := by
      have hz : ∀ j, raw22690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22690step0 = (fun i j => raw22690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22690step0 raw22690; decide +kernel
      have hl : raw22690step0Labels = raw22690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22690 raw22690Labels permutation346 hz
    mixedMoment B raw22690step0 raw22690step0Labels = mixedMoment B raw22690step1 raw22690step1Labels := by
      have hz : ∀ j, raw22690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22690step1 = (fun i j => raw22690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22690step1 raw22690step0; decide +kernel
      have hl : raw22690step1Labels = raw22690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22690step0 raw22690step0Labels permutation56 hz
    mixedMoment B raw22690step1 raw22690step1Labels = mixedMoment B raw22690step2 raw22690step2Labels := by
      have ha : raw22690step2 = (fun i j => raw22690step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22690step2 raw22690step1; decide +kernel
      have hl : raw22690step2Labels = raw22690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22690step1 raw22690step1Labels permutation9 permutation3
    _ = mixedMoment B node589 node589Labels := by rfl

def raw22691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22691 raw22691Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22691 raw22691Labels = mixedMoment B raw22691step0 raw22691step0Labels := by
      have hz : ∀ j, raw22691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22691step0 = (fun i j => raw22691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22691step0 raw22691; decide +kernel
      have hl : raw22691step0Labels = raw22691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22691 raw22691Labels permutation346 hz
    mixedMoment B raw22691step0 raw22691step0Labels = mixedMoment B raw22691step1 raw22691step1Labels := by
      have ha : raw22691step1 = (fun i j => raw22691step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22691step1 raw22691step0; decide +kernel
      have hl : raw22691step1Labels = raw22691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22691step0 raw22691step0Labels permutation33 permutation3
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw22692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22692 raw22692Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22692 raw22692Labels = mixedMoment B raw22692step0 raw22692step0Labels := by
      have hz : ∀ j, raw22692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22692step0 = (fun i j => raw22692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22692step0 raw22692; decide +kernel
      have hl : raw22692step0Labels = raw22692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22692 raw22692Labels permutation265 hz
    mixedMoment B raw22692step0 raw22692step0Labels = mixedMoment B raw22692step1 raw22692step1Labels := by
      have ha : raw22692step1 = (fun i j => raw22692step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22692step1 raw22692step0; decide +kernel
      have hl : raw22692step1Labels = raw22692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22692step0 raw22692step0Labels permutation33 permutation3
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw22693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw22693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22693 raw22693Labels = mixedMoment B node1176 node1176Labels := by
  calc
    mixedMoment B raw22693 raw22693Labels = mixedMoment B raw22693step0 raw22693step0Labels := by
      have hz : ∀ j, raw22693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22693step0 = (fun i j => raw22693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22693step0 raw22693; decide +kernel
      have hl : raw22693step0Labels = raw22693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22693 raw22693Labels permutation346 hz
    mixedMoment B raw22693step0 raw22693step0Labels = mixedMoment B raw22693step1 raw22693step1Labels := by
      have hz : ∀ j, raw22693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22693step1 = (fun i j => raw22693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22693step1 raw22693step0; decide +kernel
      have hl : raw22693step1Labels = raw22693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22693step0 raw22693step0Labels permutation56 hz
    mixedMoment B raw22693step1 raw22693step1Labels = mixedMoment B raw22693step2 raw22693step2Labels := by
      have ha : raw22693step2 = (fun i j => raw22693step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22693step2 raw22693step1; decide +kernel
      have hl : raw22693step2Labels = raw22693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22693step1 raw22693step1Labels permutation9 permutation3
    _ = mixedMoment B node1176 node1176Labels := by rfl

def raw22694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22694step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22694 raw22694Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw22694 raw22694Labels = mixedMoment B raw22694step0 raw22694step0Labels := by
      have hz : ∀ j, raw22694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22694step0 = (fun i j => raw22694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22694step0 raw22694; decide +kernel
      have hl : raw22694step0Labels = raw22694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22694 raw22694Labels permutation346 hz
    mixedMoment B raw22694step0 raw22694step0Labels = mixedMoment B raw22694step1 raw22694step1Labels := by
      have hz : ∀ j, raw22694step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22694step1 = (fun i j => raw22694step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22694step1 raw22694step0; decide +kernel
      have hl : raw22694step1Labels = raw22694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22694step0 raw22694step0Labels permutation56 hz
    mixedMoment B raw22694step1 raw22694step1Labels = mixedMoment B raw22694step2 raw22694step2Labels := by
      have ha : raw22694step2 = (fun i j => raw22694step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22694step2 raw22694step1; decide +kernel
      have hl : raw22694step2Labels = raw22694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22694step1 raw22694step1Labels permutation9 permutation3
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw22695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22695 raw22695Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw22695 raw22695Labels = mixedMoment B raw22695step0 raw22695step0Labels := by
      have hz : ∀ j, raw22695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22695step0 = (fun i j => raw22695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22695step0 raw22695; decide +kernel
      have hl : raw22695step0Labels = raw22695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22695 raw22695Labels permutation346 hz
    mixedMoment B raw22695step0 raw22695step0Labels = mixedMoment B raw22695step1 raw22695step1Labels := by
      have hz : ∀ j, raw22695step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22695step1 = (fun i j => raw22695step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22695step1 raw22695step0; decide +kernel
      have hl : raw22695step1Labels = raw22695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22695step0 raw22695step0Labels permutation56 hz
    mixedMoment B raw22695step1 raw22695step1Labels = mixedMoment B raw22695step2 raw22695step2Labels := by
      have ha : raw22695step2 = (fun i j => raw22695step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22695step2 raw22695step1; decide +kernel
      have hl : raw22695step2Labels = raw22695step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22695step1 raw22695step1Labels permutation8 permutation3
    _ = mixedMoment B node588 node588Labels := by rfl

def raw22696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22696 raw22696Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw22696 raw22696Labels = mixedMoment B raw22696step0 raw22696step0Labels := by
      have hz : ∀ j, raw22696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22696step0 = (fun i j => raw22696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22696step0 raw22696; decide +kernel
      have hl : raw22696step0Labels = raw22696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22696 raw22696Labels permutation346 hz
    mixedMoment B raw22696step0 raw22696step0Labels = mixedMoment B raw22696step1 raw22696step1Labels := by
      have ha : raw22696step1 = (fun i j => raw22696step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22696step1 raw22696step0; decide +kernel
      have hl : raw22696step1Labels = raw22696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22696step0 raw22696step0Labels permutation32 permutation3
    _ = mixedMoment B node1119 node1119Labels := by rfl

def raw22697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22697 raw22697Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw22697 raw22697Labels = mixedMoment B raw22697step0 raw22697step0Labels := by
      have hz : ∀ j, raw22697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22697step0 = (fun i j => raw22697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22697step0 raw22697; decide +kernel
      have hl : raw22697step0Labels = raw22697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22697 raw22697Labels permutation265 hz
    mixedMoment B raw22697step0 raw22697step0Labels = mixedMoment B raw22697step1 raw22697step1Labels := by
      have ha : raw22697step1 = (fun i j => raw22697step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22697step1 raw22697step0; decide +kernel
      have hl : raw22697step1Labels = raw22697step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22697step0 raw22697step0Labels permutation32 permutation3
    _ = mixedMoment B node1119 node1119Labels := by rfl

def raw22698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw22698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22698 raw22698Labels = mixedMoment B node1175 node1175Labels := by
  calc
    mixedMoment B raw22698 raw22698Labels = mixedMoment B raw22698step0 raw22698step0Labels := by
      have hz : ∀ j, raw22698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22698step0 = (fun i j => raw22698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22698step0 raw22698; decide +kernel
      have hl : raw22698step0Labels = raw22698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22698 raw22698Labels permutation346 hz
    mixedMoment B raw22698step0 raw22698step0Labels = mixedMoment B raw22698step1 raw22698step1Labels := by
      have hz : ∀ j, raw22698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22698step1 = (fun i j => raw22698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22698step1 raw22698step0; decide +kernel
      have hl : raw22698step1Labels = raw22698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22698step0 raw22698step0Labels permutation56 hz
    mixedMoment B raw22698step1 raw22698step1Labels = mixedMoment B raw22698step2 raw22698step2Labels := by
      have ha : raw22698step2 = (fun i j => raw22698step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22698step2 raw22698step1; decide +kernel
      have hl : raw22698step2Labels = raw22698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22698step1 raw22698step1Labels permutation8 permutation3
    _ = mixedMoment B node1175 node1175Labels := by rfl

def raw22699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22699step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw22699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22699step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22699step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22699 raw22699Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw22699 raw22699Labels = mixedMoment B raw22699step0 raw22699step0Labels := by
      have hz : ∀ j, raw22699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22699step0 = (fun i j => raw22699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22699step0 raw22699; decide +kernel
      have hl : raw22699step0Labels = raw22699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699 raw22699Labels permutation346 hz
    mixedMoment B raw22699step0 raw22699step0Labels = mixedMoment B raw22699step1 raw22699step1Labels := by
      have hz : ∀ j, raw22699step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22699step1 = (fun i j => raw22699step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22699step1 raw22699step0; decide +kernel
      have hl : raw22699step1Labels = raw22699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22699step0 raw22699step0Labels permutation56 hz
    mixedMoment B raw22699step1 raw22699step1Labels = mixedMoment B raw22699step2 raw22699step2Labels := by
      have ha : raw22699step2 = (fun i j => raw22699step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22699step2 raw22699step1; decide +kernel
      have hl : raw22699step2Labels = raw22699step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22699step1 raw22699step1Labels permutation9 permutation7
    mixedMoment B raw22699step2 raw22699step2Labels = mixedMoment B raw22699step3 raw22699step3Labels := by
      have ha : raw22699step3 = -raw22699step2 := by apply Matrix.ext; change ∀ i j, raw22699step3 i j = -(raw22699step2 i j); unfold raw22699step3 raw22699step2; decide +kernel
      have hl : raw22699step3Labels = raw22699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22699step3 raw22699step3Labels = mixedMoment B raw22699step4 raw22699step4Labels := by
      have ha : raw22699step4 = raw22699step3 := by apply Matrix.ext; unfold raw22699step4 raw22699step3; decide +kernel
      have hl : raw22699step3Labels = labelEmbedding1 ∘ raw22699step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22699step3 raw22699step3Labels raw22699step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw22700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22700 raw22700Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw22700 raw22700Labels = mixedMoment B raw22700step0 raw22700step0Labels := by
      have hz : ∀ j, raw22700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22700step0 = (fun i j => raw22700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22700step0 raw22700; decide +kernel
      have hl : raw22700step0Labels = raw22700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22700 raw22700Labels permutation346 hz
    mixedMoment B raw22700step0 raw22700step0Labels = mixedMoment B raw22700step1 raw22700step1Labels := by
      have ha : raw22700step1 = (fun i j => raw22700step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22700step1 raw22700step0; decide +kernel
      have hl : raw22700step1Labels = raw22700step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22700step0 raw22700step0Labels permutation46 permutation5
    mixedMoment B raw22700step1 raw22700step1Labels = mixedMoment B raw22700step2 raw22700step2Labels := by
      have ha : raw22700step2 = -raw22700step1 := by apply Matrix.ext; change ∀ i j, raw22700step2 i j = -(raw22700step1 i j); unfold raw22700step2 raw22700step1; decide +kernel
      have hl : raw22700step2Labels = raw22700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22700step2 raw22700step2Labels = mixedMoment B raw22700step3 raw22700step3Labels := by
      have ha : raw22700step3 = raw22700step2 := by apply Matrix.ext; unfold raw22700step3 raw22700step2; decide +kernel
      have hl : raw22700step2Labels = labelEmbedding1 ∘ raw22700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22700step2 raw22700step2Labels raw22700step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw22701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22701step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22701 raw22701Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw22701 raw22701Labels = mixedMoment B raw22701step0 raw22701step0Labels := by
      have ha : raw22701step0 = (fun i j => raw22701 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22701step0 raw22701; decide +kernel
      have hl : raw22701step0Labels = raw22701Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22701 raw22701Labels permutation190 permutation5
    mixedMoment B raw22701step0 raw22701step0Labels = mixedMoment B raw22701step1 raw22701step1Labels := by
      have ha : raw22701step1 = -raw22701step0 := by apply Matrix.ext; change ∀ i j, raw22701step1 i j = -(raw22701step0 i j); unfold raw22701step1 raw22701step0; decide +kernel
      have hl : raw22701step1Labels = raw22701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22701step1 raw22701step1Labels = mixedMoment B raw22701step2 raw22701step2Labels := by
      have ha : raw22701step2 = raw22701step1 := by apply Matrix.ext; unfold raw22701step2 raw22701step1; decide +kernel
      have hl : raw22701step1Labels = labelEmbedding1 ∘ raw22701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22701step1 raw22701step1Labels raw22701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw22702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22702step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22702 raw22702Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw22702 raw22702Labels = mixedMoment B raw22702step0 raw22702step0Labels := by
      have hz : ∀ j, raw22702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22702step0 = (fun i j => raw22702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22702step0 raw22702; decide +kernel
      have hl : raw22702step0Labels = raw22702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22702 raw22702Labels permutation346 hz
    mixedMoment B raw22702step0 raw22702step0Labels = mixedMoment B raw22702step1 raw22702step1Labels := by
      have ha : raw22702step1 = (fun i j => raw22702step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22702step1 raw22702step0; decide +kernel
      have hl : raw22702step1Labels = raw22702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22702step0 raw22702step0Labels permutation39 permutation7
    mixedMoment B raw22702step1 raw22702step1Labels = mixedMoment B raw22702step2 raw22702step2Labels := by
      have ha : raw22702step2 = -raw22702step1 := by apply Matrix.ext; change ∀ i j, raw22702step2 i j = -(raw22702step1 i j); unfold raw22702step2 raw22702step1; decide +kernel
      have hl : raw22702step2Labels = raw22702step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22702step2 raw22702step2Labels = mixedMoment B raw22702step3 raw22702step3Labels := by
      have ha : raw22702step3 = raw22702step2 := by apply Matrix.ext; unfold raw22702step3 raw22702step2; decide +kernel
      have hl : raw22702step2Labels = labelEmbedding1 ∘ raw22702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22702step2 raw22702step2Labels raw22702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw22703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22703 raw22703Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw22703 raw22703Labels = mixedMoment B raw22703step0 raw22703step0Labels := by
      have hz : ∀ j, raw22703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22703step0 = (fun i j => raw22703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22703step0 raw22703; decide +kernel
      have hl : raw22703step0Labels = raw22703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22703 raw22703Labels permutation346 hz
    mixedMoment B raw22703step0 raw22703step0Labels = mixedMoment B raw22703step1 raw22703step1Labels := by
      have ha : raw22703step1 = (fun i j => raw22703step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22703step1 raw22703step0; decide +kernel
      have hl : raw22703step1Labels = raw22703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22703step0 raw22703step0Labels permutation39 permutation7
    mixedMoment B raw22703step1 raw22703step1Labels = mixedMoment B raw22703step2 raw22703step2Labels := by
      have ha : raw22703step2 = -raw22703step1 := by apply Matrix.ext; change ∀ i j, raw22703step2 i j = -(raw22703step1 i j); unfold raw22703step2 raw22703step1; decide +kernel
      have hl : raw22703step2Labels = raw22703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22703step2 raw22703step2Labels = mixedMoment B raw22703step3 raw22703step3Labels := by
      have ha : raw22703step3 = raw22703step2 := by apply Matrix.ext; unfold raw22703step3 raw22703step2; decide +kernel
      have hl : raw22703step2Labels = labelEmbedding1 ∘ raw22703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22703step2 raw22703step2Labels raw22703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw22704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22704 raw22704Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw22704 raw22704Labels = mixedMoment B raw22704step0 raw22704step0Labels := by
      have hz : ∀ j, raw22704 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22704step0 = (fun i j => raw22704 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22704step0 raw22704; decide +kernel
      have hl : raw22704step0Labels = raw22704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22704 raw22704Labels permutation265 hz
    mixedMoment B raw22704step0 raw22704step0Labels = mixedMoment B raw22704step1 raw22704step1Labels := by
      have ha : raw22704step1 = (fun i j => raw22704step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22704step1 raw22704step0; decide +kernel
      have hl : raw22704step1Labels = raw22704step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22704step0 raw22704step0Labels permutation46 permutation5
    mixedMoment B raw22704step1 raw22704step1Labels = mixedMoment B raw22704step2 raw22704step2Labels := by
      have ha : raw22704step2 = -raw22704step1 := by apply Matrix.ext; change ∀ i j, raw22704step2 i j = -(raw22704step1 i j); unfold raw22704step2 raw22704step1; decide +kernel
      have hl : raw22704step2Labels = raw22704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22704step2 raw22704step2Labels = mixedMoment B raw22704step3 raw22704step3Labels := by
      have ha : raw22704step3 = raw22704step2 := by apply Matrix.ext; unfold raw22704step3 raw22704step2; decide +kernel
      have hl : raw22704step2Labels = labelEmbedding1 ∘ raw22704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22704step2 raw22704step2Labels raw22704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw22705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw22705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw22705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22705 raw22705Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw22705 raw22705Labels = mixedMoment B raw22705step0 raw22705step0Labels := by
      have ha : raw22705step0 = (fun i j => raw22705 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22705step0 raw22705; decide +kernel
      have hl : raw22705step0Labels = raw22705Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22705 raw22705Labels permutation166 permutation5
    mixedMoment B raw22705step0 raw22705step0Labels = mixedMoment B raw22705step1 raw22705step1Labels := by
      have ha : raw22705step1 = -raw22705step0 := by apply Matrix.ext; change ∀ i j, raw22705step1 i j = -(raw22705step0 i j); unfold raw22705step1 raw22705step0; decide +kernel
      have hl : raw22705step1Labels = raw22705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22705step1 raw22705step1Labels = mixedMoment B raw22705step2 raw22705step2Labels := by
      have ha : raw22705step2 = raw22705step1 := by apply Matrix.ext; unfold raw22705step2 raw22705step1; decide +kernel
      have hl : raw22705step1Labels = labelEmbedding1 ∘ raw22705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22705step1 raw22705step1Labels raw22705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw22706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw22706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw22706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22706 raw22706Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw22706 raw22706Labels = mixedMoment B raw22706step0 raw22706step0Labels := by
      have hz : ∀ j, raw22706 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22706step0 = (fun i j => raw22706 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22706step0 raw22706; decide +kernel
      have hl : raw22706step0Labels = raw22706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22706 raw22706Labels permutation265 hz
    mixedMoment B raw22706step0 raw22706step0Labels = mixedMoment B raw22706step1 raw22706step1Labels := by
      have ha : raw22706step1 = (fun i j => raw22706step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22706step1 raw22706step0; decide +kernel
      have hl : raw22706step1Labels = raw22706step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22706step0 raw22706step0Labels permutation39 permutation7
    mixedMoment B raw22706step1 raw22706step1Labels = mixedMoment B raw22706step2 raw22706step2Labels := by
      have ha : raw22706step2 = -raw22706step1 := by apply Matrix.ext; change ∀ i j, raw22706step2 i j = -(raw22706step1 i j); unfold raw22706step2 raw22706step1; decide +kernel
      have hl : raw22706step2Labels = raw22706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22706step2 raw22706step2Labels = mixedMoment B raw22706step3 raw22706step3Labels := by
      have ha : raw22706step3 = raw22706step2 := by apply Matrix.ext; unfold raw22706step3 raw22706step2; decide +kernel
      have hl : raw22706step2Labels = labelEmbedding1 ∘ raw22706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22706step2 raw22706step2Labels raw22706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw22707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22707 raw22707Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw22707 raw22707Labels = mixedMoment B raw22707step0 raw22707step0Labels := by
      have hz : ∀ j, raw22707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22707step0 = (fun i j => raw22707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22707step0 raw22707; decide +kernel
      have hl : raw22707step0Labels = raw22707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22707 raw22707Labels permutation265 hz
    mixedMoment B raw22707step0 raw22707step0Labels = mixedMoment B raw22707step1 raw22707step1Labels := by
      have ha : raw22707step1 = (fun i j => raw22707step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22707step1 raw22707step0; decide +kernel
      have hl : raw22707step1Labels = raw22707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22707step0 raw22707step0Labels permutation39 permutation7
    mixedMoment B raw22707step1 raw22707step1Labels = mixedMoment B raw22707step2 raw22707step2Labels := by
      have ha : raw22707step2 = -raw22707step1 := by apply Matrix.ext; change ∀ i j, raw22707step2 i j = -(raw22707step1 i j); unfold raw22707step2 raw22707step1; decide +kernel
      have hl : raw22707step2Labels = raw22707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22707step2 raw22707step2Labels = mixedMoment B raw22707step3 raw22707step3Labels := by
      have ha : raw22707step3 = raw22707step2 := by apply Matrix.ext; unfold raw22707step3 raw22707step2; decide +kernel
      have hl : raw22707step2Labels = labelEmbedding1 ∘ raw22707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22707step2 raw22707step2Labels raw22707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw22708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22708step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22708step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22708step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22708 raw22708Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw22708 raw22708Labels = mixedMoment B raw22708step0 raw22708step0Labels := by
      have hz : ∀ j, raw22708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22708step0 = (fun i j => raw22708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22708step0 raw22708; decide +kernel
      have hl : raw22708step0Labels = raw22708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22708 raw22708Labels permutation346 hz
    mixedMoment B raw22708step0 raw22708step0Labels = mixedMoment B raw22708step1 raw22708step1Labels := by
      have hz : ∀ j, raw22708step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22708step1 = (fun i j => raw22708step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22708step1 raw22708step0; decide +kernel
      have hl : raw22708step1Labels = raw22708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22708step0 raw22708step0Labels permutation56 hz
    mixedMoment B raw22708step1 raw22708step1Labels = mixedMoment B raw22708step2 raw22708step2Labels := by
      have ha : raw22708step2 = (fun i j => raw22708step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22708step2 raw22708step1; decide +kernel
      have hl : raw22708step2Labels = raw22708step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22708step1 raw22708step1Labels permutation11 permutation5
    mixedMoment B raw22708step2 raw22708step2Labels = mixedMoment B raw22708step3 raw22708step3Labels := by
      have ha : raw22708step3 = -raw22708step2 := by apply Matrix.ext; change ∀ i j, raw22708step3 i j = -(raw22708step2 i j); unfold raw22708step3 raw22708step2; decide +kernel
      have hl : raw22708step3Labels = raw22708step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22708step3 raw22708step3Labels = mixedMoment B raw22708step4 raw22708step4Labels := by
      have ha : raw22708step4 = raw22708step3 := by apply Matrix.ext; unfold raw22708step4 raw22708step3; decide +kernel
      have hl : raw22708step3Labels = labelEmbedding1 ∘ raw22708step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22708step3 raw22708step3Labels raw22708step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw22709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22709 raw22709Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw22709 raw22709Labels = mixedMoment B raw22709step0 raw22709step0Labels := by
      have hz : ∀ j, raw22709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22709step0 = (fun i j => raw22709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22709step0 raw22709; decide +kernel
      have hl : raw22709step0Labels = raw22709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22709 raw22709Labels permutation346 hz
    mixedMoment B raw22709step0 raw22709step0Labels = mixedMoment B raw22709step1 raw22709step1Labels := by
      have ha : raw22709step1 = (fun i j => raw22709step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22709step1 raw22709step0; decide +kernel
      have hl : raw22709step1Labels = raw22709step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22709step0 raw22709step0Labels permutation35 permutation5
    mixedMoment B raw22709step1 raw22709step1Labels = mixedMoment B raw22709step2 raw22709step2Labels := by
      have ha : raw22709step2 = -raw22709step1 := by apply Matrix.ext; change ∀ i j, raw22709step2 i j = -(raw22709step1 i j); unfold raw22709step2 raw22709step1; decide +kernel
      have hl : raw22709step2Labels = raw22709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22709step2 raw22709step2Labels = mixedMoment B raw22709step3 raw22709step3Labels := by
      have ha : raw22709step3 = raw22709step2 := by apply Matrix.ext; unfold raw22709step3 raw22709step2; decide +kernel
      have hl : raw22709step2Labels = labelEmbedding1 ∘ raw22709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22709step2 raw22709step2Labels raw22709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

def raw22710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw22710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw22710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22710 raw22710Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw22710 raw22710Labels = mixedMoment B raw22710step0 raw22710step0Labels := by
      have hz : ∀ j, raw22710 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22710step0 = (fun i j => raw22710 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22710step0 raw22710; decide +kernel
      have hl : raw22710step0Labels = raw22710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22710 raw22710Labels permutation265 hz
    mixedMoment B raw22710step0 raw22710step0Labels = mixedMoment B raw22710step1 raw22710step1Labels := by
      have ha : raw22710step1 = (fun i j => raw22710step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22710step1 raw22710step0; decide +kernel
      have hl : raw22710step1Labels = raw22710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22710step0 raw22710step0Labels permutation35 permutation5
    mixedMoment B raw22710step1 raw22710step1Labels = mixedMoment B raw22710step2 raw22710step2Labels := by
      have ha : raw22710step2 = -raw22710step1 := by apply Matrix.ext; change ∀ i j, raw22710step2 i j = -(raw22710step1 i j); unfold raw22710step2 raw22710step1; decide +kernel
      have hl : raw22710step2Labels = raw22710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22710step2 raw22710step2Labels = mixedMoment B raw22710step3 raw22710step3Labels := by
      have ha : raw22710step3 = raw22710step2 := by apply Matrix.ext; unfold raw22710step3 raw22710step2; decide +kernel
      have hl : raw22710step2Labels = labelEmbedding1 ∘ raw22710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22710step2 raw22710step2Labels raw22710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

def raw22711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22711step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22711step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22711 raw22711Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw22711 raw22711Labels = mixedMoment B raw22711step0 raw22711step0Labels := by
      have hz : ∀ j, raw22711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22711step0 = (fun i j => raw22711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22711step0 raw22711; decide +kernel
      have hl : raw22711step0Labels = raw22711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22711 raw22711Labels permutation346 hz
    mixedMoment B raw22711step0 raw22711step0Labels = mixedMoment B raw22711step1 raw22711step1Labels := by
      have hz : ∀ j, raw22711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22711step1 = (fun i j => raw22711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22711step1 raw22711step0; decide +kernel
      have hl : raw22711step1Labels = raw22711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22711step0 raw22711step0Labels permutation56 hz
    mixedMoment B raw22711step1 raw22711step1Labels = mixedMoment B raw22711step2 raw22711step2Labels := by
      have ha : raw22711step2 = (fun i j => raw22711step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22711step2 raw22711step1; decide +kernel
      have hl : raw22711step2Labels = raw22711step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22711step1 raw22711step1Labels permutation9 permutation7
    mixedMoment B raw22711step2 raw22711step2Labels = mixedMoment B raw22711step3 raw22711step3Labels := by
      have ha : raw22711step3 = -raw22711step2 := by apply Matrix.ext; change ∀ i j, raw22711step3 i j = -(raw22711step2 i j); unfold raw22711step3 raw22711step2; decide +kernel
      have hl : raw22711step3Labels = raw22711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22711step3 raw22711step3Labels = mixedMoment B raw22711step4 raw22711step4Labels := by
      have ha : raw22711step4 = raw22711step3 := by apply Matrix.ext; unfold raw22711step4 raw22711step3; decide +kernel
      have hl : raw22711step3Labels = labelEmbedding1 ∘ raw22711step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22711step3 raw22711step3Labels raw22711step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw22712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22712step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22712step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22712step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22712step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22712 raw22712Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw22712 raw22712Labels = mixedMoment B raw22712step0 raw22712step0Labels := by
      have hz : ∀ j, raw22712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22712step0 = (fun i j => raw22712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22712step0 raw22712; decide +kernel
      have hl : raw22712step0Labels = raw22712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22712 raw22712Labels permutation346 hz
    mixedMoment B raw22712step0 raw22712step0Labels = mixedMoment B raw22712step1 raw22712step1Labels := by
      have hz : ∀ j, raw22712step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22712step1 = (fun i j => raw22712step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22712step1 raw22712step0; decide +kernel
      have hl : raw22712step1Labels = raw22712step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22712step0 raw22712step0Labels permutation56 hz
    mixedMoment B raw22712step1 raw22712step1Labels = mixedMoment B raw22712step2 raw22712step2Labels := by
      have ha : raw22712step2 = (fun i j => raw22712step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22712step2 raw22712step1; decide +kernel
      have hl : raw22712step2Labels = raw22712step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22712step1 raw22712step1Labels permutation9 permutation5
    mixedMoment B raw22712step2 raw22712step2Labels = mixedMoment B raw22712step3 raw22712step3Labels := by
      have ha : raw22712step3 = -raw22712step2 := by apply Matrix.ext; change ∀ i j, raw22712step3 i j = -(raw22712step2 i j); unfold raw22712step3 raw22712step2; decide +kernel
      have hl : raw22712step3Labels = raw22712step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22712step3 raw22712step3Labels = mixedMoment B raw22712step4 raw22712step4Labels := by
      have ha : raw22712step4 = raw22712step3 := by apply Matrix.ext; unfold raw22712step4 raw22712step3; decide +kernel
      have hl : raw22712step3Labels = labelEmbedding1 ∘ raw22712step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22712step3 raw22712step3Labels raw22712step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw22713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22713step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22713step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22713 raw22713Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw22713 raw22713Labels = mixedMoment B raw22713step0 raw22713step0Labels := by
      have hz : ∀ j, raw22713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22713step0 = (fun i j => raw22713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22713step0 raw22713; decide +kernel
      have hl : raw22713step0Labels = raw22713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22713 raw22713Labels permutation346 hz
    mixedMoment B raw22713step0 raw22713step0Labels = mixedMoment B raw22713step1 raw22713step1Labels := by
      have ha : raw22713step1 = (fun i j => raw22713step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22713step1 raw22713step0; decide +kernel
      have hl : raw22713step1Labels = raw22713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22713step0 raw22713step0Labels permutation33 permutation5
    mixedMoment B raw22713step1 raw22713step1Labels = mixedMoment B raw22713step2 raw22713step2Labels := by
      have ha : raw22713step2 = -raw22713step1 := by apply Matrix.ext; change ∀ i j, raw22713step2 i j = -(raw22713step1 i j); unfold raw22713step2 raw22713step1; decide +kernel
      have hl : raw22713step2Labels = raw22713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22713step2 raw22713step2Labels = mixedMoment B raw22713step3 raw22713step3Labels := by
      have ha : raw22713step3 = raw22713step2 := by apply Matrix.ext; unfold raw22713step3 raw22713step2; decide +kernel
      have hl : raw22713step2Labels = labelEmbedding1 ∘ raw22713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22713step2 raw22713step2Labels raw22713step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw22714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw22714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw22714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22714 raw22714Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw22714 raw22714Labels = mixedMoment B raw22714step0 raw22714step0Labels := by
      have hz : ∀ j, raw22714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22714step0 = (fun i j => raw22714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22714step0 raw22714; decide +kernel
      have hl : raw22714step0Labels = raw22714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22714 raw22714Labels permutation265 hz
    mixedMoment B raw22714step0 raw22714step0Labels = mixedMoment B raw22714step1 raw22714step1Labels := by
      have ha : raw22714step1 = (fun i j => raw22714step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22714step1 raw22714step0; decide +kernel
      have hl : raw22714step1Labels = raw22714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22714step0 raw22714step0Labels permutation33 permutation5
    mixedMoment B raw22714step1 raw22714step1Labels = mixedMoment B raw22714step2 raw22714step2Labels := by
      have ha : raw22714step2 = -raw22714step1 := by apply Matrix.ext; change ∀ i j, raw22714step2 i j = -(raw22714step1 i j); unfold raw22714step2 raw22714step1; decide +kernel
      have hl : raw22714step2Labels = raw22714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22714step2 raw22714step2Labels = mixedMoment B raw22714step3 raw22714step3Labels := by
      have ha : raw22714step3 = raw22714step2 := by apply Matrix.ext; unfold raw22714step3 raw22714step2; decide +kernel
      have hl : raw22714step2Labels = labelEmbedding1 ∘ raw22714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22714step2 raw22714step2Labels raw22714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw22715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22715step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw22715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22715step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw22715step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22715 raw22715Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw22715 raw22715Labels = mixedMoment B raw22715step0 raw22715step0Labels := by
      have hz : ∀ j, raw22715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22715step0 = (fun i j => raw22715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22715step0 raw22715; decide +kernel
      have hl : raw22715step0Labels = raw22715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22715 raw22715Labels permutation346 hz
    mixedMoment B raw22715step0 raw22715step0Labels = mixedMoment B raw22715step1 raw22715step1Labels := by
      have hz : ∀ j, raw22715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22715step1 = (fun i j => raw22715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22715step1 raw22715step0; decide +kernel
      have hl : raw22715step1Labels = raw22715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22715step0 raw22715step0Labels permutation56 hz
    mixedMoment B raw22715step1 raw22715step1Labels = mixedMoment B raw22715step2 raw22715step2Labels := by
      have ha : raw22715step2 = (fun i j => raw22715step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22715step2 raw22715step1; decide +kernel
      have hl : raw22715step2Labels = raw22715step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22715step1 raw22715step1Labels permutation9 permutation7
    mixedMoment B raw22715step2 raw22715step2Labels = mixedMoment B raw22715step3 raw22715step3Labels := by
      have ha : raw22715step3 = -raw22715step2 := by apply Matrix.ext; change ∀ i j, raw22715step3 i j = -(raw22715step2 i j); unfold raw22715step3 raw22715step2; decide +kernel
      have hl : raw22715step3Labels = raw22715step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22715step3 raw22715step3Labels = mixedMoment B raw22715step4 raw22715step4Labels := by
      have ha : raw22715step4 = raw22715step3 := by apply Matrix.ext; unfold raw22715step4 raw22715step3; decide +kernel
      have hl : raw22715step3Labels = labelEmbedding1 ∘ raw22715step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22715step3 raw22715step3Labels raw22715step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw22716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw22716step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22716step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22716step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22716 raw22716Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw22716 raw22716Labels = mixedMoment B raw22716step0 raw22716step0Labels := by
      have hz : ∀ j, raw22716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22716step0 = (fun i j => raw22716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22716step0 raw22716; decide +kernel
      have hl : raw22716step0Labels = raw22716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22716 raw22716Labels permutation346 hz
    mixedMoment B raw22716step0 raw22716step0Labels = mixedMoment B raw22716step1 raw22716step1Labels := by
      have hz : ∀ j, raw22716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22716step1 = (fun i j => raw22716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22716step1 raw22716step0; decide +kernel
      have hl : raw22716step1Labels = raw22716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22716step0 raw22716step0Labels permutation56 hz
    mixedMoment B raw22716step1 raw22716step1Labels = mixedMoment B raw22716step2 raw22716step2Labels := by
      have ha : raw22716step2 = (fun i j => raw22716step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22716step2 raw22716step1; decide +kernel
      have hl : raw22716step2Labels = raw22716step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22716step1 raw22716step1Labels permutation9 permutation7
    mixedMoment B raw22716step2 raw22716step2Labels = mixedMoment B raw22716step3 raw22716step3Labels := by
      have ha : raw22716step3 = -raw22716step2 := by apply Matrix.ext; change ∀ i j, raw22716step3 i j = -(raw22716step2 i j); unfold raw22716step3 raw22716step2; decide +kernel
      have hl : raw22716step3Labels = raw22716step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22716step3 raw22716step3Labels = mixedMoment B raw22716step4 raw22716step4Labels := by
      have ha : raw22716step4 = raw22716step3 := by apply Matrix.ext; unfold raw22716step4 raw22716step3; decide +kernel
      have hl : raw22716step3Labels = labelEmbedding1 ∘ raw22716step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22716step3 raw22716step3Labels raw22716step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw22717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22717 raw22717Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw22717 raw22717Labels = mixedMoment B raw22717step0 raw22717step0Labels := by
      have hz : ∀ j, raw22717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22717step0 = (fun i j => raw22717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22717step0 raw22717; decide +kernel
      have hl : raw22717step0Labels = raw22717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22717 raw22717Labels permutation346 hz
    mixedMoment B raw22717step0 raw22717step0Labels = mixedMoment B raw22717step1 raw22717step1Labels := by
      have hz : ∀ j, raw22717step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22717step1 = (fun i j => raw22717step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22717step1 raw22717step0; decide +kernel
      have hl : raw22717step1Labels = raw22717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22717step0 raw22717step0Labels permutation56 hz
    mixedMoment B raw22717step1 raw22717step1Labels = mixedMoment B raw22717step2 raw22717step2Labels := by
      have ha : raw22717step2 = (fun i j => raw22717step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22717step2 raw22717step1; decide +kernel
      have hl : raw22717step2Labels = raw22717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22717step1 raw22717step1Labels permutation10 permutation5
    mixedMoment B raw22717step2 raw22717step2Labels = mixedMoment B raw22717step3 raw22717step3Labels := by
      have ha : raw22717step3 = -raw22717step2 := by apply Matrix.ext; change ∀ i j, raw22717step3 i j = -(raw22717step2 i j); unfold raw22717step3 raw22717step2; decide +kernel
      have hl : raw22717step3Labels = raw22717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22717step3 raw22717step3Labels = mixedMoment B raw22717step4 raw22717step4Labels := by
      have ha : raw22717step4 = raw22717step3 := by apply Matrix.ext; unfold raw22717step4 raw22717step3; decide +kernel
      have hl : raw22717step3Labels = labelEmbedding1 ∘ raw22717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22717step3 raw22717step3Labels raw22717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw22718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22718 raw22718Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw22718 raw22718Labels = mixedMoment B raw22718step0 raw22718step0Labels := by
      have hz : ∀ j, raw22718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22718step0 = (fun i j => raw22718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22718step0 raw22718; decide +kernel
      have hl : raw22718step0Labels = raw22718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22718 raw22718Labels permutation346 hz
    mixedMoment B raw22718step0 raw22718step0Labels = mixedMoment B raw22718step1 raw22718step1Labels := by
      have ha : raw22718step1 = (fun i j => raw22718step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22718step1 raw22718step0; decide +kernel
      have hl : raw22718step1Labels = raw22718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22718step0 raw22718step0Labels permutation34 permutation5
    mixedMoment B raw22718step1 raw22718step1Labels = mixedMoment B raw22718step2 raw22718step2Labels := by
      have ha : raw22718step2 = -raw22718step1 := by apply Matrix.ext; change ∀ i j, raw22718step2 i j = -(raw22718step1 i j); unfold raw22718step2 raw22718step1; decide +kernel
      have hl : raw22718step2Labels = raw22718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22718step2 raw22718step2Labels = mixedMoment B raw22718step3 raw22718step3Labels := by
      have ha : raw22718step3 = raw22718step2 := by apply Matrix.ext; unfold raw22718step3 raw22718step2; decide +kernel
      have hl : raw22718step2Labels = labelEmbedding1 ∘ raw22718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22718step2 raw22718step2Labels raw22718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw22719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw22719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw22719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22719 raw22719Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw22719 raw22719Labels = mixedMoment B raw22719step0 raw22719step0Labels := by
      have hz : ∀ j, raw22719 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22719step0 = (fun i j => raw22719 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22719step0 raw22719; decide +kernel
      have hl : raw22719step0Labels = raw22719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22719 raw22719Labels permutation265 hz
    mixedMoment B raw22719step0 raw22719step0Labels = mixedMoment B raw22719step1 raw22719step1Labels := by
      have ha : raw22719step1 = (fun i j => raw22719step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw22719step1 raw22719step0; decide +kernel
      have hl : raw22719step1Labels = raw22719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22719step0 raw22719step0Labels permutation34 permutation5
    mixedMoment B raw22719step1 raw22719step1Labels = mixedMoment B raw22719step2 raw22719step2Labels := by
      have ha : raw22719step2 = -raw22719step1 := by apply Matrix.ext; change ∀ i j, raw22719step2 i j = -(raw22719step1 i j); unfold raw22719step2 raw22719step1; decide +kernel
      have hl : raw22719step2Labels = raw22719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22719step2 raw22719step2Labels = mixedMoment B raw22719step3 raw22719step3Labels := by
      have ha : raw22719step3 = raw22719step2 := by apply Matrix.ext; unfold raw22719step3 raw22719step2; decide +kernel
      have hl : raw22719step2Labels = labelEmbedding1 ∘ raw22719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22719step2 raw22719step2Labels raw22719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw22720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw22720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw22720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22720 raw22720Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw22720 raw22720Labels = mixedMoment B raw22720step0 raw22720step0Labels := by
      have hz : ∀ j, raw22720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22720step0 = (fun i j => raw22720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22720step0 raw22720; decide +kernel
      have hl : raw22720step0Labels = raw22720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22720 raw22720Labels permutation346 hz
    mixedMoment B raw22720step0 raw22720step0Labels = mixedMoment B raw22720step1 raw22720step1Labels := by
      have hz : ∀ j, raw22720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22720step1 = (fun i j => raw22720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22720step1 raw22720step0; decide +kernel
      have hl : raw22720step1Labels = raw22720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22720step0 raw22720step0Labels permutation56 hz
    mixedMoment B raw22720step1 raw22720step1Labels = mixedMoment B raw22720step2 raw22720step2Labels := by
      have ha : raw22720step2 = (fun i j => raw22720step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22720step2 raw22720step1; decide +kernel
      have hl : raw22720step2Labels = raw22720step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22720step1 raw22720step1Labels permutation9 permutation7
    mixedMoment B raw22720step2 raw22720step2Labels = mixedMoment B raw22720step3 raw22720step3Labels := by
      have ha : raw22720step3 = -raw22720step2 := by apply Matrix.ext; change ∀ i j, raw22720step3 i j = -(raw22720step2 i j); unfold raw22720step3 raw22720step2; decide +kernel
      have hl : raw22720step3Labels = raw22720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22720step3 raw22720step3Labels = mixedMoment B raw22720step4 raw22720step4Labels := by
      have ha : raw22720step4 = raw22720step3 := by apply Matrix.ext; unfold raw22720step4 raw22720step3; decide +kernel
      have hl : raw22720step3Labels = labelEmbedding1 ∘ raw22720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22720step3 raw22720step3Labels raw22720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw22721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22721 raw22721Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw22721 raw22721Labels = mixedMoment B raw22721step0 raw22721step0Labels := by
      have hz : ∀ j, raw22721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22721step0 = (fun i j => raw22721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22721step0 raw22721; decide +kernel
      have hl : raw22721step0Labels = raw22721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22721 raw22721Labels permutation346 hz
    mixedMoment B raw22721step0 raw22721step0Labels = mixedMoment B raw22721step1 raw22721step1Labels := by
      have ha : raw22721step1 = (fun i j => raw22721step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22721step1 raw22721step0; decide +kernel
      have hl : raw22721step1Labels = raw22721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22721step0 raw22721step0Labels permutation39 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

def raw22722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22722 raw22722Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw22722 raw22722Labels = mixedMoment B raw22722step0 raw22722step0Labels := by
      have hz : ∀ j, raw22722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22722step0 = (fun i j => raw22722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22722step0 raw22722; decide +kernel
      have hl : raw22722step0Labels = raw22722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22722 raw22722Labels permutation265 hz
    mixedMoment B raw22722step0 raw22722step0Labels = mixedMoment B raw22722step1 raw22722step1Labels := by
      have ha : raw22722step1 = (fun i j => raw22722step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22722step1 raw22722step0; decide +kernel
      have hl : raw22722step1Labels = raw22722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22722step0 raw22722step0Labels permutation39 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

def raw22723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22723 raw22723Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw22723 raw22723Labels = mixedMoment B raw22723step0 raw22723step0Labels := by
      have hz : ∀ j, raw22723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22723step0 = (fun i j => raw22723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22723step0 raw22723; decide +kernel
      have hl : raw22723step0Labels = raw22723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22723 raw22723Labels permutation346 hz
    mixedMoment B raw22723step0 raw22723step0Labels = mixedMoment B raw22723step1 raw22723step1Labels := by
      have hz : ∀ j, raw22723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22723step1 = (fun i j => raw22723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22723step1 raw22723step0; decide +kernel
      have hl : raw22723step1Labels = raw22723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22723step0 raw22723step0Labels permutation56 hz
    mixedMoment B raw22723step1 raw22723step1Labels = mixedMoment B raw22723step2 raw22723step2Labels := by
      have ha : raw22723step2 = (fun i j => raw22723step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22723step2 raw22723step1; decide +kernel
      have hl : raw22723step2Labels = raw22723step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22723step1 raw22723step1Labels permutation9 permutation2
    _ = mixedMoment B node642 node642Labels := by rfl

def raw22724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22724step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22724 raw22724Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw22724 raw22724Labels = mixedMoment B raw22724step0 raw22724step0Labels := by
      have hz : ∀ j, raw22724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22724step0 = (fun i j => raw22724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22724step0 raw22724; decide +kernel
      have hl : raw22724step0Labels = raw22724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22724 raw22724Labels permutation346 hz
    mixedMoment B raw22724step0 raw22724step0Labels = mixedMoment B raw22724step1 raw22724step1Labels := by
      have hz : ∀ j, raw22724step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22724step1 = (fun i j => raw22724step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22724step1 raw22724step0; decide +kernel
      have hl : raw22724step1Labels = raw22724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22724step0 raw22724step0Labels permutation56 hz
    mixedMoment B raw22724step1 raw22724step1Labels = mixedMoment B raw22724step2 raw22724step2Labels := by
      have ha : raw22724step2 = (fun i j => raw22724step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22724step2 raw22724step1; decide +kernel
      have hl : raw22724step2Labels = raw22724step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22724step1 raw22724step1Labels permutation9 permutation2
    _ = mixedMoment B node635 node635Labels := by rfl

def raw22725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22725 raw22725Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw22725 raw22725Labels = mixedMoment B raw22725step0 raw22725step0Labels := by
      have hz : ∀ j, raw22725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22725step0 = (fun i j => raw22725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22725step0 raw22725; decide +kernel
      have hl : raw22725step0Labels = raw22725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22725 raw22725Labels permutation346 hz
    mixedMoment B raw22725step0 raw22725step0Labels = mixedMoment B raw22725step1 raw22725step1Labels := by
      have hz : ∀ j, raw22725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22725step1 = (fun i j => raw22725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22725step1 raw22725step0; decide +kernel
      have hl : raw22725step1Labels = raw22725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22725step0 raw22725step0Labels permutation56 hz
    _ = mixedMoment B node636 node636Labels := by rfl

def raw22726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22726 raw22726Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw22726 raw22726Labels = mixedMoment B raw22726step0 raw22726step0Labels := by
      have ha : raw22726step0 = (fun i j => raw22726 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22726step0 raw22726; decide +kernel
      have hl : raw22726step0Labels = raw22726Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22726 raw22726Labels permutation183 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

def raw22727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22727 raw22727Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw22727 raw22727Labels = mixedMoment B raw22727step0 raw22727step0Labels := by
      have hz : ∀ j, raw22727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22727step0 = (fun i j => raw22727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22727step0 raw22727; decide +kernel
      have hl : raw22727step0Labels = raw22727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22727 raw22727Labels permutation346 hz
    mixedMoment B raw22727step0 raw22727step0Labels = mixedMoment B raw22727step1 raw22727step1Labels := by
      have ha : raw22727step1 = (fun i j => raw22727step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22727step1 raw22727step0; decide +kernel
      have hl : raw22727step1Labels = raw22727step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22727step0 raw22727step0Labels permutation39 permutation2
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw22728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22728 raw22728Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw22728 raw22728Labels = mixedMoment B raw22728step0 raw22728step0Labels := by
      have hz : ∀ j, raw22728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22728step0 = (fun i j => raw22728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22728step0 raw22728; decide +kernel
      have hl : raw22728step0Labels = raw22728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22728 raw22728Labels permutation346 hz
    mixedMoment B raw22728step0 raw22728step0Labels = mixedMoment B raw22728step1 raw22728step1Labels := by
      have ha : raw22728step1 = (fun i j => raw22728step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22728step1 raw22728step0; decide +kernel
      have hl : raw22728step1Labels = raw22728step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22728step0 raw22728step0Labels permutation38 permutation2
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw22729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22729 raw22729Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw22729 raw22729Labels = mixedMoment B raw22729step0 raw22729step0Labels := by
      have hz : ∀ j, raw22729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22729step0 = (fun i j => raw22729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22729step0 raw22729; decide +kernel
      have hl : raw22729step0Labels = raw22729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22729 raw22729Labels permutation346 hz
    mixedMoment B raw22729step0 raw22729step0Labels = mixedMoment B raw22729step1 raw22729step1Labels := by
      have ha : raw22729step1 = (fun i j => raw22729step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22729step1 raw22729step0; decide +kernel
      have hl : raw22729step1Labels = raw22729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22729step0 raw22729step0Labels permutation39 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw22730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22730 raw22730Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw22730 raw22730Labels = mixedMoment B raw22730step0 raw22730step0Labels := by
      have ha : raw22730step0 = (fun i j => raw22730 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22730step0 raw22730; decide +kernel
      have hl : raw22730step0Labels = raw22730Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22730 raw22730Labels permutation159 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

def raw22731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22731 raw22731Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw22731 raw22731Labels = mixedMoment B raw22731step0 raw22731step0Labels := by
      have hz : ∀ j, raw22731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22731step0 = (fun i j => raw22731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22731step0 raw22731; decide +kernel
      have hl : raw22731step0Labels = raw22731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22731 raw22731Labels permutation346 hz
    mixedMoment B raw22731step0 raw22731step0Labels = mixedMoment B raw22731step1 raw22731step1Labels := by
      have ha : raw22731step1 = (fun i j => raw22731step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22731step1 raw22731step0; decide +kernel
      have hl : raw22731step1Labels = raw22731step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22731step0 raw22731step0Labels permutation33 permutation2
    _ = mixedMoment B node1160 node1160Labels := by rfl

def raw22732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22732 raw22732Labels = mixedMoment B node1154 node1154Labels := by
  calc
    mixedMoment B raw22732 raw22732Labels = mixedMoment B raw22732step0 raw22732step0Labels := by
      have hz : ∀ j, raw22732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22732step0 = (fun i j => raw22732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22732step0 raw22732; decide +kernel
      have hl : raw22732step0Labels = raw22732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22732 raw22732Labels permutation346 hz
    mixedMoment B raw22732step0 raw22732step0Labels = mixedMoment B raw22732step1 raw22732step1Labels := by
      have ha : raw22732step1 = (fun i j => raw22732step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22732step1 raw22732step0; decide +kernel
      have hl : raw22732step1Labels = raw22732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22732step0 raw22732step0Labels permutation33 permutation2
    _ = mixedMoment B node1154 node1154Labels := by rfl

def raw22733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22733 raw22733Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw22733 raw22733Labels = mixedMoment B raw22733step0 raw22733step0Labels := by
      have hz : ∀ j, raw22733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22733step0 = (fun i j => raw22733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22733step0 raw22733; decide +kernel
      have hl : raw22733step0Labels = raw22733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22733 raw22733Labels permutation346 hz
    _ = mixedMoment B node1155 node1155Labels := by rfl

def raw22734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22734 raw22734Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw22734 raw22734Labels = mixedMoment B raw22734step0 raw22734step0Labels := by
      have hz : ∀ j, raw22734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22734step0 = (fun i j => raw22734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22734step0 raw22734; decide +kernel
      have hl : raw22734step0Labels = raw22734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22734 raw22734Labels permutation265 hz
    mixedMoment B raw22734step0 raw22734step0Labels = mixedMoment B raw22734step1 raw22734step1Labels := by
      have ha : raw22734step1 = (fun i j => raw22734step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22734step1 raw22734step0; decide +kernel
      have hl : raw22734step1Labels = raw22734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22734step0 raw22734step0Labels permutation33 permutation2
    _ = mixedMoment B node1160 node1160Labels := by rfl

def raw22735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22735 raw22735Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw22735 raw22735Labels = mixedMoment B raw22735step0 raw22735step0Labels := by
      have hz : ∀ j, raw22735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22735step0 = (fun i j => raw22735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22735step0 raw22735; decide +kernel
      have hl : raw22735step0Labels = raw22735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22735 raw22735Labels permutation346 hz
    mixedMoment B raw22735step0 raw22735step0Labels = mixedMoment B raw22735step1 raw22735step1Labels := by
      have hz : ∀ j, raw22735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22735step1 = (fun i j => raw22735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22735step1 raw22735step0; decide +kernel
      have hl : raw22735step1Labels = raw22735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22735step0 raw22735step0Labels permutation56 hz
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw22736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22736 raw22736Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22736 raw22736Labels = mixedMoment B raw22736step0 raw22736step0Labels := by
      have hz : ∀ j, raw22736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22736step0 = (fun i j => raw22736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22736step0 raw22736; decide +kernel
      have hl : raw22736step0Labels = raw22736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22736 raw22736Labels permutation346 hz
    mixedMoment B raw22736step0 raw22736step0Labels = mixedMoment B raw22736step1 raw22736step1Labels := by
      have hz : ∀ j, raw22736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22736step1 = (fun i j => raw22736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22736step1 raw22736step0; decide +kernel
      have hl : raw22736step1Labels = raw22736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22736step0 raw22736step0Labels permutation56 hz
    mixedMoment B raw22736step1 raw22736step1Labels = mixedMoment B raw22736step2 raw22736step2Labels := by
      have ha : raw22736step2 = (fun i j => raw22736step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22736step2 raw22736step1; decide +kernel
      have hl : raw22736step2Labels = raw22736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22736step1 raw22736step1Labels permutation9 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw22737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22737 raw22737Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw22737 raw22737Labels = mixedMoment B raw22737step0 raw22737step0Labels := by
      have hz : ∀ j, raw22737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22737step0 = (fun i j => raw22737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22737step0 raw22737; decide +kernel
      have hl : raw22737step0Labels = raw22737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22737 raw22737Labels permutation346 hz
    mixedMoment B raw22737step0 raw22737step0Labels = mixedMoment B raw22737step1 raw22737step1Labels := by
      have ha : raw22737step1 = (fun i j => raw22737step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22737step1 raw22737step0; decide +kernel
      have hl : raw22737step1Labels = raw22737step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22737step0 raw22737step0Labels permutation39 permutation3
    mixedMoment B raw22737step1 raw22737step1Labels = mixedMoment B raw22737step2 raw22737step2Labels := by
      have ha : raw22737step2 = raw22737step1 := by apply Matrix.ext; unfold raw22737step2 raw22737step1; decide +kernel
      have hl : raw22737step1Labels = labelEmbedding6 ∘ raw22737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22737step1 raw22737step1Labels raw22737step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw22738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22738 raw22738Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw22738 raw22738Labels = mixedMoment B raw22738step0 raw22738step0Labels := by
      have ha : raw22738step0 = (fun i j => raw22738 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22738step0 raw22738; decide +kernel
      have hl : raw22738step0Labels = raw22738Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22738 raw22738Labels permutation183 permutation3
    mixedMoment B raw22738step0 raw22738step0Labels = mixedMoment B raw22738step1 raw22738step1Labels := by
      have ha : raw22738step1 = raw22738step0 := by apply Matrix.ext; unfold raw22738step1 raw22738step0; decide +kernel
      have hl : raw22738step0Labels = labelEmbedding6 ∘ raw22738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22738step0 raw22738step0Labels raw22738step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw22739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22739 raw22739Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw22739 raw22739Labels = mixedMoment B raw22739step0 raw22739step0Labels := by
      have hz : ∀ j, raw22739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22739step0 = (fun i j => raw22739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22739step0 raw22739; decide +kernel
      have hl : raw22739step0Labels = raw22739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22739 raw22739Labels permutation346 hz
    mixedMoment B raw22739step0 raw22739step0Labels = mixedMoment B raw22739step1 raw22739step1Labels := by
      have ha : raw22739step1 = (fun i j => raw22739step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22739step1 raw22739step0; decide +kernel
      have hl : raw22739step1Labels = raw22739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22739step0 raw22739step0Labels permutation39 permutation3
    mixedMoment B raw22739step1 raw22739step1Labels = mixedMoment B raw22739step2 raw22739step2Labels := by
      have ha : raw22739step2 = raw22739step1 := by apply Matrix.ext; unfold raw22739step2 raw22739step1; decide +kernel
      have hl : raw22739step1Labels = labelEmbedding6 ∘ raw22739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22739step1 raw22739step1Labels raw22739step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw22740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22740 raw22740Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22740 raw22740Labels = mixedMoment B raw22740step0 raw22740step0Labels := by
      have hz : ∀ j, raw22740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22740step0 = (fun i j => raw22740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22740step0 raw22740; decide +kernel
      have hl : raw22740step0Labels = raw22740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22740 raw22740Labels permutation346 hz
    mixedMoment B raw22740step0 raw22740step0Labels = mixedMoment B raw22740step1 raw22740step1Labels := by
      have ha : raw22740step1 = (fun i j => raw22740step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22740step1 raw22740step0; decide +kernel
      have hl : raw22740step1Labels = raw22740step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22740step0 raw22740step0Labels permutation42 permutation3
    mixedMoment B raw22740step1 raw22740step1Labels = mixedMoment B raw22740step2 raw22740step2Labels := by
      have ha : raw22740step2 = raw22740step1 := by apply Matrix.ext; unfold raw22740step2 raw22740step1; decide +kernel
      have hl : raw22740step1Labels = labelEmbedding6 ∘ raw22740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22740step1 raw22740step1Labels raw22740step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw22741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22741 raw22741Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw22741 raw22741Labels = mixedMoment B raw22741step0 raw22741step0Labels := by
      have hz : ∀ j, raw22741 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22741step0 = (fun i j => raw22741 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22741step0 raw22741; decide +kernel
      have hl : raw22741step0Labels = raw22741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22741 raw22741Labels permutation265 hz
    mixedMoment B raw22741step0 raw22741step0Labels = mixedMoment B raw22741step1 raw22741step1Labels := by
      have ha : raw22741step1 = (fun i j => raw22741step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22741step1 raw22741step0; decide +kernel
      have hl : raw22741step1Labels = raw22741step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22741step0 raw22741step0Labels permutation39 permutation3
    mixedMoment B raw22741step1 raw22741step1Labels = mixedMoment B raw22741step2 raw22741step2Labels := by
      have ha : raw22741step2 = raw22741step1 := by apply Matrix.ext; unfold raw22741step2 raw22741step1; decide +kernel
      have hl : raw22741step1Labels = labelEmbedding6 ∘ raw22741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22741step1 raw22741step1Labels raw22741step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw22742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22742 raw22742Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw22742 raw22742Labels = mixedMoment B raw22742step0 raw22742step0Labels := by
      have ha : raw22742step0 = (fun i j => raw22742 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22742step0 raw22742; decide +kernel
      have hl : raw22742step0Labels = raw22742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22742 raw22742Labels permutation159 permutation3
    mixedMoment B raw22742step0 raw22742step0Labels = mixedMoment B raw22742step1 raw22742step1Labels := by
      have ha : raw22742step1 = raw22742step0 := by apply Matrix.ext; unfold raw22742step1 raw22742step0; decide +kernel
      have hl : raw22742step0Labels = labelEmbedding6 ∘ raw22742step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22742step0 raw22742step0Labels raw22742step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw22743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22743step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22743 raw22743Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw22743 raw22743Labels = mixedMoment B raw22743step0 raw22743step0Labels := by
      have hz : ∀ j, raw22743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22743step0 = (fun i j => raw22743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22743step0 raw22743; decide +kernel
      have hl : raw22743step0Labels = raw22743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22743 raw22743Labels permutation265 hz
    mixedMoment B raw22743step0 raw22743step0Labels = mixedMoment B raw22743step1 raw22743step1Labels := by
      have ha : raw22743step1 = (fun i j => raw22743step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22743step1 raw22743step0; decide +kernel
      have hl : raw22743step1Labels = raw22743step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22743step0 raw22743step0Labels permutation39 permutation3
    mixedMoment B raw22743step1 raw22743step1Labels = mixedMoment B raw22743step2 raw22743step2Labels := by
      have ha : raw22743step2 = raw22743step1 := by apply Matrix.ext; unfold raw22743step2 raw22743step1; decide +kernel
      have hl : raw22743step1Labels = labelEmbedding6 ∘ raw22743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22743step1 raw22743step1Labels raw22743step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw22744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22744 raw22744Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw22744 raw22744Labels = mixedMoment B raw22744step0 raw22744step0Labels := by
      have hz : ∀ j, raw22744 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22744step0 = (fun i j => raw22744 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22744step0 raw22744; decide +kernel
      have hl : raw22744step0Labels = raw22744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22744 raw22744Labels permutation265 hz
    mixedMoment B raw22744step0 raw22744step0Labels = mixedMoment B raw22744step1 raw22744step1Labels := by
      have ha : raw22744step1 = (fun i j => raw22744step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22744step1 raw22744step0; decide +kernel
      have hl : raw22744step1Labels = raw22744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22744step0 raw22744step0Labels permutation42 permutation3
    mixedMoment B raw22744step1 raw22744step1Labels = mixedMoment B raw22744step2 raw22744step2Labels := by
      have ha : raw22744step2 = raw22744step1 := by apply Matrix.ext; unfold raw22744step2 raw22744step1; decide +kernel
      have hl : raw22744step1Labels = labelEmbedding6 ∘ raw22744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22744step1 raw22744step1Labels raw22744step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw22745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22745step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22745 raw22745Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw22745 raw22745Labels = mixedMoment B raw22745step0 raw22745step0Labels := by
      have hz : ∀ j, raw22745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22745step0 = (fun i j => raw22745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22745step0 raw22745; decide +kernel
      have hl : raw22745step0Labels = raw22745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22745 raw22745Labels permutation346 hz
    mixedMoment B raw22745step0 raw22745step0Labels = mixedMoment B raw22745step1 raw22745step1Labels := by
      have hz : ∀ j, raw22745step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22745step1 = (fun i j => raw22745step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22745step1 raw22745step0; decide +kernel
      have hl : raw22745step1Labels = raw22745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22745step0 raw22745step0Labels permutation56 hz
    mixedMoment B raw22745step1 raw22745step1Labels = mixedMoment B raw22745step2 raw22745step2Labels := by
      have ha : raw22745step2 = (fun i j => raw22745step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22745step2 raw22745step1; decide +kernel
      have hl : raw22745step2Labels = raw22745step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22745step1 raw22745step1Labels permutation9 permutation3
    mixedMoment B raw22745step2 raw22745step2Labels = mixedMoment B raw22745step3 raw22745step3Labels := by
      have ha : raw22745step3 = raw22745step2 := by apply Matrix.ext; unfold raw22745step3 raw22745step2; decide +kernel
      have hl : raw22745step2Labels = labelEmbedding6 ∘ raw22745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22745step2 raw22745step2Labels raw22745step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw22746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22746step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22746 raw22746Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22746 raw22746Labels = mixedMoment B raw22746step0 raw22746step0Labels := by
      have hz : ∀ j, raw22746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22746step0 = (fun i j => raw22746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22746step0 raw22746; decide +kernel
      have hl : raw22746step0Labels = raw22746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22746 raw22746Labels permutation346 hz
    mixedMoment B raw22746step0 raw22746step0Labels = mixedMoment B raw22746step1 raw22746step1Labels := by
      have ha : raw22746step1 = (fun i j => raw22746step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22746step1 raw22746step0; decide +kernel
      have hl : raw22746step1Labels = raw22746step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22746step0 raw22746step0Labels permutation33 permutation3
    mixedMoment B raw22746step1 raw22746step1Labels = mixedMoment B raw22746step2 raw22746step2Labels := by
      have ha : raw22746step2 = raw22746step1 := by apply Matrix.ext; unfold raw22746step2 raw22746step1; decide +kernel
      have hl : raw22746step1Labels = labelEmbedding6 ∘ raw22746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22746step1 raw22746step1Labels raw22746step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw22747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22747 raw22747Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw22747 raw22747Labels = mixedMoment B raw22747step0 raw22747step0Labels := by
      have hz : ∀ j, raw22747 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22747step0 = (fun i j => raw22747 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22747step0 raw22747; decide +kernel
      have hl : raw22747step0Labels = raw22747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22747 raw22747Labels permutation265 hz
    mixedMoment B raw22747step0 raw22747step0Labels = mixedMoment B raw22747step1 raw22747step1Labels := by
      have ha : raw22747step1 = (fun i j => raw22747step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22747step1 raw22747step0; decide +kernel
      have hl : raw22747step1Labels = raw22747step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22747step0 raw22747step0Labels permutation33 permutation3
    mixedMoment B raw22747step1 raw22747step1Labels = mixedMoment B raw22747step2 raw22747step2Labels := by
      have ha : raw22747step2 = raw22747step1 := by apply Matrix.ext; unfold raw22747step2 raw22747step1; decide +kernel
      have hl : raw22747step1Labels = labelEmbedding6 ∘ raw22747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22747step1 raw22747step1Labels raw22747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw22748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22748step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22748 raw22748Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw22748 raw22748Labels = mixedMoment B raw22748step0 raw22748step0Labels := by
      have hz : ∀ j, raw22748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22748step0 = (fun i j => raw22748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22748step0 raw22748; decide +kernel
      have hl : raw22748step0Labels = raw22748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22748 raw22748Labels permutation346 hz
    mixedMoment B raw22748step0 raw22748step0Labels = mixedMoment B raw22748step1 raw22748step1Labels := by
      have hz : ∀ j, raw22748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22748step1 = (fun i j => raw22748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22748step1 raw22748step0; decide +kernel
      have hl : raw22748step1Labels = raw22748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22748step0 raw22748step0Labels permutation56 hz
    mixedMoment B raw22748step1 raw22748step1Labels = mixedMoment B raw22748step2 raw22748step2Labels := by
      have ha : raw22748step2 = (fun i j => raw22748step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22748step2 raw22748step1; decide +kernel
      have hl : raw22748step2Labels = raw22748step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22748step1 raw22748step1Labels permutation9 permutation3
    mixedMoment B raw22748step2 raw22748step2Labels = mixedMoment B raw22748step3 raw22748step3Labels := by
      have ha : raw22748step3 = raw22748step2 := by apply Matrix.ext; unfold raw22748step3 raw22748step2; decide +kernel
      have hl : raw22748step2Labels = labelEmbedding6 ∘ raw22748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22748step2 raw22748step2Labels raw22748step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw22749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22749step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22749 raw22749Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw22749 raw22749Labels = mixedMoment B raw22749step0 raw22749step0Labels := by
      have hz : ∀ j, raw22749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22749step0 = (fun i j => raw22749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22749step0 raw22749; decide +kernel
      have hl : raw22749step0Labels = raw22749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22749 raw22749Labels permutation346 hz
    mixedMoment B raw22749step0 raw22749step0Labels = mixedMoment B raw22749step1 raw22749step1Labels := by
      have hz : ∀ j, raw22749step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22749step1 = (fun i j => raw22749step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22749step1 raw22749step0; decide +kernel
      have hl : raw22749step1Labels = raw22749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22749step0 raw22749step0Labels permutation56 hz
    mixedMoment B raw22749step1 raw22749step1Labels = mixedMoment B raw22749step2 raw22749step2Labels := by
      have ha : raw22749step2 = (fun i j => raw22749step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22749step2 raw22749step1; decide +kernel
      have hl : raw22749step2Labels = raw22749step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22749step1 raw22749step1Labels permutation9 permutation3
    mixedMoment B raw22749step2 raw22749step2Labels = mixedMoment B raw22749step3 raw22749step3Labels := by
      have ha : raw22749step3 = raw22749step2 := by apply Matrix.ext; unfold raw22749step3 raw22749step2; decide +kernel
      have hl : raw22749step2Labels = labelEmbedding6 ∘ raw22749step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22749step2 raw22749step2Labels raw22749step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

def raw22750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22750 raw22750Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw22750 raw22750Labels = mixedMoment B raw22750step0 raw22750step0Labels := by
      have hz : ∀ j, raw22750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22750step0 = (fun i j => raw22750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22750step0 raw22750; decide +kernel
      have hl : raw22750step0Labels = raw22750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22750 raw22750Labels permutation346 hz
    mixedMoment B raw22750step0 raw22750step0Labels = mixedMoment B raw22750step1 raw22750step1Labels := by
      have ha : raw22750step1 = (fun i j => raw22750step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22750step1 raw22750step0; decide +kernel
      have hl : raw22750step1Labels = raw22750step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22750step0 raw22750step0Labels permutation33 permutation3
    mixedMoment B raw22750step1 raw22750step1Labels = mixedMoment B raw22750step2 raw22750step2Labels := by
      have ha : raw22750step2 = raw22750step1 := by apply Matrix.ext; unfold raw22750step2 raw22750step1; decide +kernel
      have hl : raw22750step1Labels = labelEmbedding6 ∘ raw22750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22750step1 raw22750step1Labels raw22750step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw22751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22751 raw22751Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw22751 raw22751Labels = mixedMoment B raw22751step0 raw22751step0Labels := by
      have hz : ∀ j, raw22751 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22751step0 = (fun i j => raw22751 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22751step0 raw22751; decide +kernel
      have hl : raw22751step0Labels = raw22751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22751 raw22751Labels permutation265 hz
    mixedMoment B raw22751step0 raw22751step0Labels = mixedMoment B raw22751step1 raw22751step1Labels := by
      have ha : raw22751step1 = (fun i j => raw22751step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22751step1 raw22751step0; decide +kernel
      have hl : raw22751step1Labels = raw22751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22751step0 raw22751step0Labels permutation33 permutation3
    mixedMoment B raw22751step1 raw22751step1Labels = mixedMoment B raw22751step2 raw22751step2Labels := by
      have ha : raw22751step2 = raw22751step1 := by apply Matrix.ext; unfold raw22751step2 raw22751step1; decide +kernel
      have hl : raw22751step1Labels = labelEmbedding6 ∘ raw22751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22751step1 raw22751step1Labels raw22751step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw22752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22752 raw22752Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw22752 raw22752Labels = mixedMoment B raw22752step0 raw22752step0Labels := by
      have hz : ∀ j, raw22752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22752step0 = (fun i j => raw22752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22752step0 raw22752; decide +kernel
      have hl : raw22752step0Labels = raw22752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22752 raw22752Labels permutation346 hz
    mixedMoment B raw22752step0 raw22752step0Labels = mixedMoment B raw22752step1 raw22752step1Labels := by
      have hz : ∀ j, raw22752step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22752step1 = (fun i j => raw22752step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22752step1 raw22752step0; decide +kernel
      have hl : raw22752step1Labels = raw22752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22752step0 raw22752step0Labels permutation56 hz
    mixedMoment B raw22752step1 raw22752step1Labels = mixedMoment B raw22752step2 raw22752step2Labels := by
      have ha : raw22752step2 = (fun i j => raw22752step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22752step2 raw22752step1; decide +kernel
      have hl : raw22752step2Labels = raw22752step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22752step1 raw22752step1Labels permutation9 permutation3
    mixedMoment B raw22752step2 raw22752step2Labels = mixedMoment B raw22752step3 raw22752step3Labels := by
      have ha : raw22752step3 = raw22752step2 := by apply Matrix.ext; unfold raw22752step3 raw22752step2; decide +kernel
      have hl : raw22752step2Labels = labelEmbedding6 ∘ raw22752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22752step2 raw22752step2Labels raw22752step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

def raw22753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22753step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22753 raw22753Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw22753 raw22753Labels = mixedMoment B raw22753step0 raw22753step0Labels := by
      have hz : ∀ j, raw22753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22753step0 = (fun i j => raw22753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22753step0 raw22753; decide +kernel
      have hl : raw22753step0Labels = raw22753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22753 raw22753Labels permutation346 hz
    mixedMoment B raw22753step0 raw22753step0Labels = mixedMoment B raw22753step1 raw22753step1Labels := by
      have hz : ∀ j, raw22753step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22753step1 = (fun i j => raw22753step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22753step1 raw22753step0; decide +kernel
      have hl : raw22753step1Labels = raw22753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22753step0 raw22753step0Labels permutation56 hz
    mixedMoment B raw22753step1 raw22753step1Labels = mixedMoment B raw22753step2 raw22753step2Labels := by
      have ha : raw22753step2 = (fun i j => raw22753step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22753step2 raw22753step1; decide +kernel
      have hl : raw22753step2Labels = raw22753step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22753step1 raw22753step1Labels permutation9 permutation3
    mixedMoment B raw22753step2 raw22753step2Labels = mixedMoment B raw22753step3 raw22753step3Labels := by
      have ha : raw22753step3 = raw22753step2 := by apply Matrix.ext; unfold raw22753step3 raw22753step2; decide +kernel
      have hl : raw22753step2Labels = labelEmbedding6 ∘ raw22753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22753step2 raw22753step2Labels raw22753step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw22754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22754 raw22754Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw22754 raw22754Labels = mixedMoment B raw22754step0 raw22754step0Labels := by
      have hz : ∀ j, raw22754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22754step0 = (fun i j => raw22754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22754step0 raw22754; decide +kernel
      have hl : raw22754step0Labels = raw22754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22754 raw22754Labels permutation346 hz
    mixedMoment B raw22754step0 raw22754step0Labels = mixedMoment B raw22754step1 raw22754step1Labels := by
      have ha : raw22754step1 = (fun i j => raw22754step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22754step1 raw22754step0; decide +kernel
      have hl : raw22754step1Labels = raw22754step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22754step0 raw22754step0Labels permutation39 permutation3
    _ = mixedMoment B node573 node573Labels := by rfl

def raw22755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22755 raw22755Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw22755 raw22755Labels = mixedMoment B raw22755step0 raw22755step0Labels := by
      have ha : raw22755step0 = (fun i j => raw22755 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22755step0 raw22755; decide +kernel
      have hl : raw22755step0Labels = raw22755Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22755 raw22755Labels permutation183 permutation3
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw22756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22756 raw22756Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw22756 raw22756Labels = mixedMoment B raw22756step0 raw22756step0Labels := by
      have hz : ∀ j, raw22756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22756step0 = (fun i j => raw22756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22756step0 raw22756; decide +kernel
      have hl : raw22756step0Labels = raw22756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22756 raw22756Labels permutation346 hz
    mixedMoment B raw22756step0 raw22756step0Labels = mixedMoment B raw22756step1 raw22756step1Labels := by
      have ha : raw22756step1 = (fun i j => raw22756step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22756step1 raw22756step0; decide +kernel
      have hl : raw22756step1Labels = raw22756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22756step0 raw22756step0Labels permutation39 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw22757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22757 raw22757Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw22757 raw22757Labels = mixedMoment B raw22757step0 raw22757step0Labels := by
      have hz : ∀ j, raw22757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22757step0 = (fun i j => raw22757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22757step0 raw22757; decide +kernel
      have hl : raw22757step0Labels = raw22757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22757 raw22757Labels permutation346 hz
    mixedMoment B raw22757step0 raw22757step0Labels = mixedMoment B raw22757step1 raw22757step1Labels := by
      have ha : raw22757step1 = (fun i j => raw22757step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22757step1 raw22757step0; decide +kernel
      have hl : raw22757step1Labels = raw22757step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22757step0 raw22757step0Labels permutation42 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw22758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22758 raw22758Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw22758 raw22758Labels = mixedMoment B raw22758step0 raw22758step0Labels := by
      have hz : ∀ j, raw22758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22758step0 = (fun i j => raw22758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22758step0 raw22758; decide +kernel
      have hl : raw22758step0Labels = raw22758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22758 raw22758Labels permutation265 hz
    mixedMoment B raw22758step0 raw22758step0Labels = mixedMoment B raw22758step1 raw22758step1Labels := by
      have ha : raw22758step1 = (fun i j => raw22758step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22758step1 raw22758step0; decide +kernel
      have hl : raw22758step1Labels = raw22758step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22758step0 raw22758step0Labels permutation39 permutation3
    _ = mixedMoment B node573 node573Labels := by rfl

def raw22759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22759 raw22759Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw22759 raw22759Labels = mixedMoment B raw22759step0 raw22759step0Labels := by
      have ha : raw22759step0 = (fun i j => raw22759 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22759step0 raw22759; decide +kernel
      have hl : raw22759step0Labels = raw22759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22759 raw22759Labels permutation159 permutation3
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw22760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22760 raw22760Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw22760 raw22760Labels = mixedMoment B raw22760step0 raw22760step0Labels := by
      have hz : ∀ j, raw22760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22760step0 = (fun i j => raw22760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22760step0 raw22760; decide +kernel
      have hl : raw22760step0Labels = raw22760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22760 raw22760Labels permutation265 hz
    mixedMoment B raw22760step0 raw22760step0Labels = mixedMoment B raw22760step1 raw22760step1Labels := by
      have ha : raw22760step1 = (fun i j => raw22760step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22760step1 raw22760step0; decide +kernel
      have hl : raw22760step1Labels = raw22760step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22760step0 raw22760step0Labels permutation39 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw22761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22761 raw22761Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw22761 raw22761Labels = mixedMoment B raw22761step0 raw22761step0Labels := by
      have hz : ∀ j, raw22761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22761step0 = (fun i j => raw22761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22761step0 raw22761; decide +kernel
      have hl : raw22761step0Labels = raw22761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22761 raw22761Labels permutation265 hz
    mixedMoment B raw22761step0 raw22761step0Labels = mixedMoment B raw22761step1 raw22761step1Labels := by
      have ha : raw22761step1 = (fun i j => raw22761step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22761step1 raw22761step0; decide +kernel
      have hl : raw22761step1Labels = raw22761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22761step0 raw22761step0Labels permutation42 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw22762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22762 raw22762Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw22762 raw22762Labels = mixedMoment B raw22762step0 raw22762step0Labels := by
      have hz : ∀ j, raw22762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22762step0 = (fun i j => raw22762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22762step0 raw22762; decide +kernel
      have hl : raw22762step0Labels = raw22762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22762 raw22762Labels permutation346 hz
    mixedMoment B raw22762step0 raw22762step0Labels = mixedMoment B raw22762step1 raw22762step1Labels := by
      have hz : ∀ j, raw22762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22762step1 = (fun i j => raw22762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22762step1 raw22762step0; decide +kernel
      have hl : raw22762step1Labels = raw22762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22762step0 raw22762step0Labels permutation56 hz
    mixedMoment B raw22762step1 raw22762step1Labels = mixedMoment B raw22762step2 raw22762step2Labels := by
      have ha : raw22762step2 = (fun i j => raw22762step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22762step2 raw22762step1; decide +kernel
      have hl : raw22762step2Labels = raw22762step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22762step1 raw22762step1Labels permutation9 permutation3
    _ = mixedMoment B node608 node608Labels := by rfl

def raw22763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22763 raw22763Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw22763 raw22763Labels = mixedMoment B raw22763step0 raw22763step0Labels := by
      have hz : ∀ j, raw22763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22763step0 = (fun i j => raw22763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22763step0 raw22763; decide +kernel
      have hl : raw22763step0Labels = raw22763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22763 raw22763Labels permutation346 hz
    mixedMoment B raw22763step0 raw22763step0Labels = mixedMoment B raw22763step1 raw22763step1Labels := by
      have ha : raw22763step1 = (fun i j => raw22763step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22763step1 raw22763step0; decide +kernel
      have hl : raw22763step1Labels = raw22763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22763step0 raw22763step0Labels permutation33 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw22764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22764 raw22764Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw22764 raw22764Labels = mixedMoment B raw22764step0 raw22764step0Labels := by
      have hz : ∀ j, raw22764 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22764step0 = (fun i j => raw22764 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22764step0 raw22764; decide +kernel
      have hl : raw22764step0Labels = raw22764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22764 raw22764Labels permutation265 hz
    mixedMoment B raw22764step0 raw22764step0Labels = mixedMoment B raw22764step1 raw22764step1Labels := by
      have ha : raw22764step1 = (fun i j => raw22764step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22764step1 raw22764step0; decide +kernel
      have hl : raw22764step1Labels = raw22764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22764step0 raw22764step0Labels permutation33 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw22765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22765step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22765 raw22765Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw22765 raw22765Labels = mixedMoment B raw22765step0 raw22765step0Labels := by
      have hz : ∀ j, raw22765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22765step0 = (fun i j => raw22765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22765step0 raw22765; decide +kernel
      have hl : raw22765step0Labels = raw22765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22765 raw22765Labels permutation346 hz
    mixedMoment B raw22765step0 raw22765step0Labels = mixedMoment B raw22765step1 raw22765step1Labels := by
      have hz : ∀ j, raw22765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22765step1 = (fun i j => raw22765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22765step1 raw22765step0; decide +kernel
      have hl : raw22765step1Labels = raw22765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22765step0 raw22765step0Labels permutation56 hz
    mixedMoment B raw22765step1 raw22765step1Labels = mixedMoment B raw22765step2 raw22765step2Labels := by
      have ha : raw22765step2 = (fun i j => raw22765step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22765step2 raw22765step1; decide +kernel
      have hl : raw22765step2Labels = raw22765step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22765step1 raw22765step1Labels permutation9 permutation3
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw22766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22766step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22766 raw22766Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw22766 raw22766Labels = mixedMoment B raw22766step0 raw22766step0Labels := by
      have hz : ∀ j, raw22766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22766step0 = (fun i j => raw22766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22766step0 raw22766; decide +kernel
      have hl : raw22766step0Labels = raw22766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22766 raw22766Labels permutation346 hz
    mixedMoment B raw22766step0 raw22766step0Labels = mixedMoment B raw22766step1 raw22766step1Labels := by
      have hz : ∀ j, raw22766step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22766step1 = (fun i j => raw22766step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22766step1 raw22766step0; decide +kernel
      have hl : raw22766step1Labels = raw22766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22766step0 raw22766step0Labels permutation56 hz
    mixedMoment B raw22766step1 raw22766step1Labels = mixedMoment B raw22766step2 raw22766step2Labels := by
      have ha : raw22766step2 = (fun i j => raw22766step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22766step2 raw22766step1; decide +kernel
      have hl : raw22766step2Labels = raw22766step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22766step1 raw22766step1Labels permutation9 permutation3
    _ = mixedMoment B node575 node575Labels := by rfl

def raw22767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22767step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22767 raw22767Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw22767 raw22767Labels = mixedMoment B raw22767step0 raw22767step0Labels := by
      have hz : ∀ j, raw22767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22767step0 = (fun i j => raw22767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22767step0 raw22767; decide +kernel
      have hl : raw22767step0Labels = raw22767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22767 raw22767Labels permutation346 hz
    mixedMoment B raw22767step0 raw22767step0Labels = mixedMoment B raw22767step1 raw22767step1Labels := by
      have ha : raw22767step1 = (fun i j => raw22767step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22767step1 raw22767step0; decide +kernel
      have hl : raw22767step1Labels = raw22767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22767step0 raw22767step0Labels permutation33 permutation3
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw22768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22768step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw22768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22768 raw22768Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw22768 raw22768Labels = mixedMoment B raw22768step0 raw22768step0Labels := by
      have hz : ∀ j, raw22768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22768step0 = (fun i j => raw22768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22768step0 raw22768; decide +kernel
      have hl : raw22768step0Labels = raw22768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22768 raw22768Labels permutation265 hz
    mixedMoment B raw22768step0 raw22768step0Labels = mixedMoment B raw22768step1 raw22768step1Labels := by
      have ha : raw22768step1 = (fun i j => raw22768step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22768step1 raw22768step0; decide +kernel
      have hl : raw22768step1Labels = raw22768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22768step0 raw22768step0Labels permutation33 permutation3
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw22769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw22769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw22769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22769 raw22769Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw22769 raw22769Labels = mixedMoment B raw22769step0 raw22769step0Labels := by
      have hz : ∀ j, raw22769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22769step0 = (fun i j => raw22769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22769step0 raw22769; decide +kernel
      have hl : raw22769step0Labels = raw22769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22769 raw22769Labels permutation346 hz
    mixedMoment B raw22769step0 raw22769step0Labels = mixedMoment B raw22769step1 raw22769step1Labels := by
      have hz : ∀ j, raw22769step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22769step1 = (fun i j => raw22769step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22769step1 raw22769step0; decide +kernel
      have hl : raw22769step1Labels = raw22769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22769step0 raw22769step0Labels permutation56 hz
    mixedMoment B raw22769step1 raw22769step1Labels = mixedMoment B raw22769step2 raw22769step2Labels := by
      have ha : raw22769step2 = (fun i j => raw22769step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22769step2 raw22769step1; decide +kernel
      have hl : raw22769step2Labels = raw22769step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22769step1 raw22769step1Labels permutation9 permutation3
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw22770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw22770step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22770step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw22770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22770 raw22770Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw22770 raw22770Labels = mixedMoment B raw22770step0 raw22770step0Labels := by
      have hz : ∀ j, raw22770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22770step0 = (fun i j => raw22770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22770step0 raw22770; decide +kernel
      have hl : raw22770step0Labels = raw22770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22770 raw22770Labels permutation346 hz
    mixedMoment B raw22770step0 raw22770step0Labels = mixedMoment B raw22770step1 raw22770step1Labels := by
      have hz : ∀ j, raw22770step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22770step1 = (fun i j => raw22770step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22770step1 raw22770step0; decide +kernel
      have hl : raw22770step1Labels = raw22770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22770step0 raw22770step0Labels permutation56 hz
    mixedMoment B raw22770step1 raw22770step1Labels = mixedMoment B raw22770step2 raw22770step2Labels := by
      have ha : raw22770step2 = (fun i j => raw22770step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22770step2 raw22770step1; decide +kernel
      have hl : raw22770step2Labels = raw22770step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22770step1 raw22770step1Labels permutation9 permutation3
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw22771 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22771step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22771 raw22771Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw22771 raw22771Labels = mixedMoment B raw22771step0 raw22771step0Labels := by
      have hz : ∀ j, raw22771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22771step0 = (fun i j => raw22771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22771step0 raw22771; decide +kernel
      have hl : raw22771step0Labels = raw22771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22771 raw22771Labels permutation346 hz
    mixedMoment B raw22771step0 raw22771step0Labels = mixedMoment B raw22771step1 raw22771step1Labels := by
      have ha : raw22771step1 = (fun i j => raw22771step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22771step1 raw22771step0; decide +kernel
      have hl : raw22771step1Labels = raw22771step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22771step0 raw22771step0Labels permutation32 permutation7
    mixedMoment B raw22771step1 raw22771step1Labels = mixedMoment B raw22771step2 raw22771step2Labels := by
      have ha : raw22771step2 = raw22771step1 := by apply Matrix.ext; unfold raw22771step2 raw22771step1; decide +kernel
      have hl : raw22771step1Labels = labelEmbedding10 ∘ raw22771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22771step1 raw22771step1Labels raw22771step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw22772 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22772step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22772 raw22772Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw22772 raw22772Labels = mixedMoment B raw22772step0 raw22772step0Labels := by
      have hz : ∀ j, raw22772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22772step0 = (fun i j => raw22772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22772step0 raw22772; decide +kernel
      have hl : raw22772step0Labels = raw22772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22772 raw22772Labels permutation265 hz
    mixedMoment B raw22772step0 raw22772step0Labels = mixedMoment B raw22772step1 raw22772step1Labels := by
      have ha : raw22772step1 = (fun i j => raw22772step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22772step1 raw22772step0; decide +kernel
      have hl : raw22772step1Labels = raw22772step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22772step0 raw22772step0Labels permutation32 permutation7
    mixedMoment B raw22772step1 raw22772step1Labels = mixedMoment B raw22772step2 raw22772step2Labels := by
      have ha : raw22772step2 = raw22772step1 := by apply Matrix.ext; unfold raw22772step2 raw22772step1; decide +kernel
      have hl : raw22772step1Labels = labelEmbedding10 ∘ raw22772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22772step1 raw22772step1Labels raw22772step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw22773 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22773step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22773 raw22773Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw22773 raw22773Labels = mixedMoment B raw22773step0 raw22773step0Labels := by
      have hz : ∀ j, raw22773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22773step0 = (fun i j => raw22773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22773step0 raw22773; decide +kernel
      have hl : raw22773step0Labels = raw22773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22773 raw22773Labels permutation346 hz
    mixedMoment B raw22773step0 raw22773step0Labels = mixedMoment B raw22773step1 raw22773step1Labels := by
      have hz : ∀ j, raw22773step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22773step1 = (fun i j => raw22773step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22773step1 raw22773step0; decide +kernel
      have hl : raw22773step1Labels = raw22773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22773step0 raw22773step0Labels permutation56 hz
    mixedMoment B raw22773step1 raw22773step1Labels = mixedMoment B raw22773step2 raw22773step2Labels := by
      have ha : raw22773step2 = (fun i j => raw22773step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22773step2 raw22773step1; decide +kernel
      have hl : raw22773step2Labels = raw22773step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22773step1 raw22773step1Labels permutation8 permutation7
    mixedMoment B raw22773step2 raw22773step2Labels = mixedMoment B raw22773step3 raw22773step3Labels := by
      have ha : raw22773step3 = raw22773step2 := by apply Matrix.ext; unfold raw22773step3 raw22773step2; decide +kernel
      have hl : raw22773step2Labels = labelEmbedding10 ∘ raw22773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22773step2 raw22773step2Labels raw22773step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw22774 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22774step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22774 raw22774Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22774 raw22774Labels = mixedMoment B raw22774step0 raw22774step0Labels := by
      have hz : ∀ j, raw22774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22774step0 = (fun i j => raw22774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22774step0 raw22774; decide +kernel
      have hl : raw22774step0Labels = raw22774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22774 raw22774Labels permutation346 hz
    mixedMoment B raw22774step0 raw22774step0Labels = mixedMoment B raw22774step1 raw22774step1Labels := by
      have hz : ∀ j, raw22774step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22774step1 = (fun i j => raw22774step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22774step1 raw22774step0; decide +kernel
      have hl : raw22774step1Labels = raw22774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22774step0 raw22774step0Labels permutation56 hz
    mixedMoment B raw22774step1 raw22774step1Labels = mixedMoment B raw22774step2 raw22774step2Labels := by
      have ha : raw22774step2 = (fun i j => raw22774step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22774step2 raw22774step1; decide +kernel
      have hl : raw22774step2Labels = raw22774step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22774step1 raw22774step1Labels permutation8 permutation7
    mixedMoment B raw22774step2 raw22774step2Labels = mixedMoment B raw22774step3 raw22774step3Labels := by
      have ha : raw22774step3 = raw22774step2 := by apply Matrix.ext; unfold raw22774step3 raw22774step2; decide +kernel
      have hl : raw22774step2Labels = labelEmbedding10 ∘ raw22774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22774step2 raw22774step2Labels raw22774step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22775 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22775 raw22775Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw22775 raw22775Labels = mixedMoment B raw22775step0 raw22775step0Labels := by
      have hz : ∀ j, raw22775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22775step0 = (fun i j => raw22775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22775step0 raw22775; decide +kernel
      have hl : raw22775step0Labels = raw22775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22775 raw22775Labels permutation346 hz
    mixedMoment B raw22775step0 raw22775step0Labels = mixedMoment B raw22775step1 raw22775step1Labels := by
      have ha : raw22775step1 = (fun i j => raw22775step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22775step1 raw22775step0; decide +kernel
      have hl : raw22775step1Labels = raw22775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22775step0 raw22775step0Labels permutation39 permutation6
    mixedMoment B raw22775step1 raw22775step1Labels = mixedMoment B raw22775step2 raw22775step2Labels := by
      have ha : raw22775step2 = raw22775step1 := by apply Matrix.ext; unfold raw22775step2 raw22775step1; decide +kernel
      have hl : raw22775step1Labels = labelEmbedding9 ∘ raw22775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22775step1 raw22775step1Labels raw22775step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw22776 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22776step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22776 raw22776Labels = mixedMoment B node4578 node4578Labels := by
  calc
    mixedMoment B raw22776 raw22776Labels = mixedMoment B raw22776step0 raw22776step0Labels := by
      have ha : raw22776step0 = (fun i j => raw22776 (permutation183 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22776step0 raw22776; decide +kernel
      have hl : raw22776step0Labels = raw22776Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22776 raw22776Labels permutation183 permutation6
    mixedMoment B raw22776step0 raw22776step0Labels = mixedMoment B raw22776step1 raw22776step1Labels := by
      have ha : raw22776step1 = raw22776step0 := by apply Matrix.ext; unfold raw22776step1 raw22776step0; decide +kernel
      have hl : raw22776step0Labels = labelEmbedding9 ∘ raw22776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22776step0 raw22776step0Labels raw22776step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4578 node4578Labels := by rfl

def raw22777 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22777step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22777 raw22777Labels = mixedMoment B node4565 node4565Labels := by
  calc
    mixedMoment B raw22777 raw22777Labels = mixedMoment B raw22777step0 raw22777step0Labels := by
      have hz : ∀ j, raw22777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22777step0 = (fun i j => raw22777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22777step0 raw22777; decide +kernel
      have hl : raw22777step0Labels = raw22777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22777 raw22777Labels permutation346 hz
    mixedMoment B raw22777step0 raw22777step0Labels = mixedMoment B raw22777step1 raw22777step1Labels := by
      have ha : raw22777step1 = (fun i j => raw22777step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22777step1 raw22777step0; decide +kernel
      have hl : raw22777step1Labels = raw22777step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22777step0 raw22777step0Labels permutation39 permutation6
    mixedMoment B raw22777step1 raw22777step1Labels = mixedMoment B raw22777step2 raw22777step2Labels := by
      have ha : raw22777step2 = raw22777step1 := by apply Matrix.ext; unfold raw22777step2 raw22777step1; decide +kernel
      have hl : raw22777step1Labels = labelEmbedding9 ∘ raw22777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22777step1 raw22777step1Labels raw22777step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4565 node4565Labels := by rfl

def raw22778 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22778step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22778 raw22778Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22778 raw22778Labels = mixedMoment B raw22778step0 raw22778step0Labels := by
      have hz : ∀ j, raw22778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22778step0 = (fun i j => raw22778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22778step0 raw22778; decide +kernel
      have hl : raw22778step0Labels = raw22778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22778 raw22778Labels permutation346 hz
    mixedMoment B raw22778step0 raw22778step0Labels = mixedMoment B raw22778step1 raw22778step1Labels := by
      have ha : raw22778step1 = (fun i j => raw22778step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22778step1 raw22778step0; decide +kernel
      have hl : raw22778step1Labels = raw22778step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22778step0 raw22778step0Labels permutation39 permutation6
    mixedMoment B raw22778step1 raw22778step1Labels = mixedMoment B raw22778step2 raw22778step2Labels := by
      have ha : raw22778step2 = raw22778step1 := by apply Matrix.ext; unfold raw22778step2 raw22778step1; decide +kernel
      have hl : raw22778step1Labels = labelEmbedding9 ∘ raw22778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22778step1 raw22778step1Labels raw22778step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22779 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22779 raw22779Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw22779 raw22779Labels = mixedMoment B raw22779step0 raw22779step0Labels := by
      have hz : ∀ j, raw22779 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22779step0 = (fun i j => raw22779 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22779step0 raw22779; decide +kernel
      have hl : raw22779step0Labels = raw22779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22779 raw22779Labels permutation265 hz
    mixedMoment B raw22779step0 raw22779step0Labels = mixedMoment B raw22779step1 raw22779step1Labels := by
      have ha : raw22779step1 = (fun i j => raw22779step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22779step1 raw22779step0; decide +kernel
      have hl : raw22779step1Labels = raw22779step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22779step0 raw22779step0Labels permutation39 permutation6
    mixedMoment B raw22779step1 raw22779step1Labels = mixedMoment B raw22779step2 raw22779step2Labels := by
      have ha : raw22779step2 = raw22779step1 := by apply Matrix.ext; unfold raw22779step2 raw22779step1; decide +kernel
      have hl : raw22779step1Labels = labelEmbedding9 ∘ raw22779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22779step1 raw22779step1Labels raw22779step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw22780 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22780step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22780 raw22780Labels = mixedMoment B node4578 node4578Labels := by
  calc
    mixedMoment B raw22780 raw22780Labels = mixedMoment B raw22780step0 raw22780step0Labels := by
      have ha : raw22780step0 = (fun i j => raw22780 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22780step0 raw22780; decide +kernel
      have hl : raw22780step0Labels = raw22780Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22780 raw22780Labels permutation159 permutation6
    mixedMoment B raw22780step0 raw22780step0Labels = mixedMoment B raw22780step1 raw22780step1Labels := by
      have ha : raw22780step1 = raw22780step0 := by apply Matrix.ext; unfold raw22780step1 raw22780step0; decide +kernel
      have hl : raw22780step0Labels = labelEmbedding9 ∘ raw22780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22780step0 raw22780step0Labels raw22780step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4578 node4578Labels := by rfl

def raw22781 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22781step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22781 raw22781Labels = mixedMoment B node4565 node4565Labels := by
  calc
    mixedMoment B raw22781 raw22781Labels = mixedMoment B raw22781step0 raw22781step0Labels := by
      have hz : ∀ j, raw22781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22781step0 = (fun i j => raw22781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22781step0 raw22781; decide +kernel
      have hl : raw22781step0Labels = raw22781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22781 raw22781Labels permutation265 hz
    mixedMoment B raw22781step0 raw22781step0Labels = mixedMoment B raw22781step1 raw22781step1Labels := by
      have ha : raw22781step1 = (fun i j => raw22781step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22781step1 raw22781step0; decide +kernel
      have hl : raw22781step1Labels = raw22781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22781step0 raw22781step0Labels permutation39 permutation6
    mixedMoment B raw22781step1 raw22781step1Labels = mixedMoment B raw22781step2 raw22781step2Labels := by
      have ha : raw22781step2 = raw22781step1 := by apply Matrix.ext; unfold raw22781step2 raw22781step1; decide +kernel
      have hl : raw22781step1Labels = labelEmbedding9 ∘ raw22781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22781step1 raw22781step1Labels raw22781step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4565 node4565Labels := by rfl

def raw22782 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22782step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22782 raw22782Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22782 raw22782Labels = mixedMoment B raw22782step0 raw22782step0Labels := by
      have hz : ∀ j, raw22782 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22782step0 = (fun i j => raw22782 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22782step0 raw22782; decide +kernel
      have hl : raw22782step0Labels = raw22782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22782 raw22782Labels permutation265 hz
    mixedMoment B raw22782step0 raw22782step0Labels = mixedMoment B raw22782step1 raw22782step1Labels := by
      have ha : raw22782step1 = (fun i j => raw22782step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22782step1 raw22782step0; decide +kernel
      have hl : raw22782step1Labels = raw22782step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22782step0 raw22782step0Labels permutation39 permutation6
    mixedMoment B raw22782step1 raw22782step1Labels = mixedMoment B raw22782step2 raw22782step2Labels := by
      have ha : raw22782step2 = raw22782step1 := by apply Matrix.ext; unfold raw22782step2 raw22782step1; decide +kernel
      have hl : raw22782step1Labels = labelEmbedding9 ∘ raw22782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22782step1 raw22782step1Labels raw22782step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22783 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22783step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22783step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22783 raw22783Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw22783 raw22783Labels = mixedMoment B raw22783step0 raw22783step0Labels := by
      have hz : ∀ j, raw22783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22783step0 = (fun i j => raw22783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22783step0 raw22783; decide +kernel
      have hl : raw22783step0Labels = raw22783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22783 raw22783Labels permutation346 hz
    mixedMoment B raw22783step0 raw22783step0Labels = mixedMoment B raw22783step1 raw22783step1Labels := by
      have hz : ∀ j, raw22783step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22783step1 = (fun i j => raw22783step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22783step1 raw22783step0; decide +kernel
      have hl : raw22783step1Labels = raw22783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22783step0 raw22783step0Labels permutation56 hz
    mixedMoment B raw22783step1 raw22783step1Labels = mixedMoment B raw22783step2 raw22783step2Labels := by
      have ha : raw22783step2 = (fun i j => raw22783step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22783step2 raw22783step1; decide +kernel
      have hl : raw22783step2Labels = raw22783step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22783step1 raw22783step1Labels permutation9 permutation6
    mixedMoment B raw22783step2 raw22783step2Labels = mixedMoment B raw22783step3 raw22783step3Labels := by
      have ha : raw22783step3 = raw22783step2 := by apply Matrix.ext; unfold raw22783step3 raw22783step2; decide +kernel
      have hl : raw22783step2Labels = labelEmbedding9 ∘ raw22783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22783step2 raw22783step2Labels raw22783step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
