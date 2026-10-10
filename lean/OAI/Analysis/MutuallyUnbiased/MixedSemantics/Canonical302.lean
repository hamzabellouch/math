import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38656 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw38656Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38656step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw38656step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38656step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38656 raw38656Labels = mixedMoment B node3248 node3248Labels := by
  calc
    mixedMoment B raw38656 raw38656Labels = mixedMoment B raw38656step0 raw38656step0Labels := by
      have ha : raw38656step0 = (fun i j => raw38656 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38656step0 raw38656; decide +kernel
      have hl : raw38656step0Labels = raw38656Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38656 raw38656Labels permutation8 permutation7
    mixedMoment B raw38656step0 raw38656step0Labels = mixedMoment B raw38656step1 raw38656step1Labels := by
      have ha : raw38656step1 = -raw38656step0 := by apply Matrix.ext; change ∀ i j, raw38656step1 i j = -(raw38656step0 i j); unfold raw38656step1 raw38656step0; decide +kernel
      have hl : raw38656step1Labels = raw38656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38656step1 raw38656step1Labels = mixedMoment B raw38656step2 raw38656step2Labels := by
      have ha : raw38656step2 = raw38656step1 := by apply Matrix.ext; unfold raw38656step2 raw38656step1; decide +kernel
      have hl : raw38656step1Labels = labelEmbedding4 ∘ raw38656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38656step1 raw38656step1Labels raw38656step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3248 node3248Labels := by rfl

def raw38657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38657Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38657 raw38657Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw38657 raw38657Labels = mixedMoment B raw38657step0 raw38657step0Labels := by
      have ha : raw38657step0 = raw38657 := by apply Matrix.ext; unfold raw38657step0 raw38657; decide +kernel
      have hl : raw38657Labels = labelEmbedding2 ∘ raw38657step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38657 raw38657Labels raw38657step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw38658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38658Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38658step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38658step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38658 raw38658Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw38658 raw38658Labels = mixedMoment B raw38658step0 raw38658step0Labels := by
      have ha : raw38658step0 = (fun i j => raw38658 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38658step0 raw38658; decide +kernel
      have hl : raw38658step0Labels = raw38658Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38658 raw38658Labels permutation152 permutation7
    mixedMoment B raw38658step0 raw38658step0Labels = mixedMoment B raw38658step1 raw38658step1Labels := by
      have ha : raw38658step1 = -raw38658step0 := by apply Matrix.ext; change ∀ i j, raw38658step1 i j = -(raw38658step0 i j); unfold raw38658step1 raw38658step0; decide +kernel
      have hl : raw38658step1Labels = raw38658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38658step1 raw38658step1Labels = mixedMoment B raw38658step2 raw38658step2Labels := by
      have ha : raw38658step2 = raw38658step1 := by apply Matrix.ext; unfold raw38658step2 raw38658step1; decide +kernel
      have hl : raw38658step1Labels = labelEmbedding4 ∘ raw38658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38658step1 raw38658step1Labels raw38658step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3281 node3281Labels := by rfl

def raw38659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38659Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38659 raw38659Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw38659 raw38659Labels = mixedMoment B raw38659step0 raw38659step0Labels := by
      have ha : raw38659step0 = raw38659 := by apply Matrix.ext; unfold raw38659step0 raw38659; decide +kernel
      have hl : raw38659Labels = labelEmbedding2 ∘ raw38659step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38659 raw38659Labels raw38659step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw38660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38660Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw38660step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw38660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38660 raw38660Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw38660 raw38660Labels = mixedMoment B raw38660step0 raw38660step0Labels := by
      have ha : raw38660step0 = (fun i j => raw38660 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38660step0 raw38660; decide +kernel
      have hl : raw38660step0Labels = raw38660Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38660 raw38660Labels permutation149 permutation7
    mixedMoment B raw38660step0 raw38660step0Labels = mixedMoment B raw38660step1 raw38660step1Labels := by
      have ha : raw38660step1 = raw38660step0 := by apply Matrix.ext; unfold raw38660step1 raw38660step0; decide +kernel
      have hl : raw38660step0Labels = labelEmbedding4 ∘ raw38660step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38660step0 raw38660step0Labels raw38660step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1942 node1942Labels := by rfl

def raw38661 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38661Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38661 raw38661Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw38661 raw38661Labels = mixedMoment B raw38661step0 raw38661step0Labels := by
      have ha : raw38661step0 = raw38661 := by apply Matrix.ext; unfold raw38661step0 raw38661; decide +kernel
      have hl : raw38661Labels = labelEmbedding2 ∘ raw38661step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38661 raw38661Labels raw38661step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw38662 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38662Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw38662step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38662step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38662 raw38662Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw38662 raw38662Labels = mixedMoment B raw38662step0 raw38662step0Labels := by
      have ha : raw38662step0 = (fun i j => raw38662 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38662step0 raw38662; decide +kernel
      have hl : raw38662step0Labels = raw38662Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38662 raw38662Labels permutation32 permutation7
    mixedMoment B raw38662step0 raw38662step0Labels = mixedMoment B raw38662step1 raw38662step1Labels := by
      have ha : raw38662step1 = -raw38662step0 := by apply Matrix.ext; change ∀ i j, raw38662step1 i j = -(raw38662step0 i j); unfold raw38662step1 raw38662step0; decide +kernel
      have hl : raw38662step1Labels = raw38662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38662step1 raw38662step1Labels = mixedMoment B raw38662step2 raw38662step2Labels := by
      have ha : raw38662step2 = raw38662step1 := by apply Matrix.ext; unfold raw38662step2 raw38662step1; decide +kernel
      have hl : raw38662step1Labels = labelEmbedding4 ∘ raw38662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38662step1 raw38662step1Labels raw38662step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3284 node3284Labels := by rfl

def raw38663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38663Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38663 raw38663Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw38663 raw38663Labels = mixedMoment B raw38663step0 raw38663step0Labels := by
      have ha : raw38663step0 = raw38663 := by apply Matrix.ext; unfold raw38663step0 raw38663; decide +kernel
      have hl : raw38663Labels = labelEmbedding2 ∘ raw38663step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38663 raw38663Labels raw38663step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw38664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38664Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38664step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38664step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38664step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38664 raw38664Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw38664 raw38664Labels = mixedMoment B raw38664step0 raw38664step0Labels := by
      have ha : raw38664step0 = (fun i j => raw38664 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38664step0 raw38664; decide +kernel
      have hl : raw38664step0Labels = raw38664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38664 raw38664Labels permutation152 permutation7
    mixedMoment B raw38664step0 raw38664step0Labels = mixedMoment B raw38664step1 raw38664step1Labels := by
      have ha : raw38664step1 = -raw38664step0 := by apply Matrix.ext; change ∀ i j, raw38664step1 i j = -(raw38664step0 i j); unfold raw38664step1 raw38664step0; decide +kernel
      have hl : raw38664step1Labels = raw38664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38664step1 raw38664step1Labels = mixedMoment B raw38664step2 raw38664step2Labels := by
      have ha : raw38664step2 = raw38664step1 := by apply Matrix.ext; unfold raw38664step2 raw38664step1; decide +kernel
      have hl : raw38664step1Labels = labelEmbedding4 ∘ raw38664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38664step1 raw38664step1Labels raw38664step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw38665 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38665Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38665 raw38665Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw38665 raw38665Labels = mixedMoment B raw38665step0 raw38665step0Labels := by
      have ha : raw38665step0 = raw38665 := by apply Matrix.ext; unfold raw38665step0 raw38665; decide +kernel
      have hl : raw38665Labels = labelEmbedding2 ∘ raw38665step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38665 raw38665Labels raw38665step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw38666 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38666Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38666step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38666step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38666 raw38666Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw38666 raw38666Labels = mixedMoment B raw38666step0 raw38666step0Labels := by
      have ha : raw38666step0 = (fun i j => raw38666 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38666step0 raw38666; decide +kernel
      have hl : raw38666step0Labels = raw38666Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38666 raw38666Labels permutation32 permutation7
    mixedMoment B raw38666step0 raw38666step0Labels = mixedMoment B raw38666step1 raw38666step1Labels := by
      have ha : raw38666step1 = -raw38666step0 := by apply Matrix.ext; change ∀ i j, raw38666step1 i j = -(raw38666step0 i j); unfold raw38666step1 raw38666step0; decide +kernel
      have hl : raw38666step1Labels = raw38666step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38666step1 raw38666step1Labels = mixedMoment B raw38666step2 raw38666step2Labels := by
      have ha : raw38666step2 = raw38666step1 := by apply Matrix.ext; unfold raw38666step2 raw38666step1; decide +kernel
      have hl : raw38666step1Labels = labelEmbedding4 ∘ raw38666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38666step1 raw38666step1Labels raw38666step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw38667 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw38667Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38667step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw38667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38667 raw38667Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw38667 raw38667Labels = mixedMoment B raw38667step0 raw38667step0Labels := by
      have ha : raw38667step0 = raw38667 := by apply Matrix.ext; unfold raw38667step0 raw38667; decide +kernel
      have hl : raw38667Labels = labelEmbedding2 ∘ raw38667step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38667 raw38667Labels raw38667step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw38668 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw38668Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38668step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw38668step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw38668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38668 raw38668Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw38668 raw38668Labels = mixedMoment B raw38668step0 raw38668step0Labels := by
      have ha : raw38668step0 = (fun i j => raw38668 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38668step0 raw38668; decide +kernel
      have hl : raw38668step0Labels = raw38668Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38668 raw38668Labels permutation31 permutation7
    mixedMoment B raw38668step0 raw38668step0Labels = mixedMoment B raw38668step1 raw38668step1Labels := by
      have ha : raw38668step1 = raw38668step0 := by apply Matrix.ext; unfold raw38668step1 raw38668step0; decide +kernel
      have hl : raw38668step0Labels = labelEmbedding4 ∘ raw38668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38668step0 raw38668step0Labels raw38668step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw38669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38669Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38669 raw38669Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw38669 raw38669Labels = mixedMoment B raw38669step0 raw38669step0Labels := by
      have ha : raw38669step0 = raw38669 := by apply Matrix.ext; unfold raw38669step0 raw38669; decide +kernel
      have hl : raw38669Labels = labelEmbedding2 ∘ raw38669step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38669 raw38669Labels raw38669step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw38670 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38670Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38670step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38670step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38670 raw38670Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw38670 raw38670Labels = mixedMoment B raw38670step0 raw38670step0Labels := by
      have ha : raw38670step0 = (fun i j => raw38670 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38670step0 raw38670; decide +kernel
      have hl : raw38670step0Labels = raw38670Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38670 raw38670Labels permutation32 permutation7
    mixedMoment B raw38670step0 raw38670step0Labels = mixedMoment B raw38670step1 raw38670step1Labels := by
      have ha : raw38670step1 = -raw38670step0 := by apply Matrix.ext; change ∀ i j, raw38670step1 i j = -(raw38670step0 i j); unfold raw38670step1 raw38670step0; decide +kernel
      have hl : raw38670step1Labels = raw38670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38670step1 raw38670step1Labels = mixedMoment B raw38670step2 raw38670step2Labels := by
      have ha : raw38670step2 = raw38670step1 := by apply Matrix.ext; unfold raw38670step2 raw38670step1; decide +kernel
      have hl : raw38670step1Labels = labelEmbedding4 ∘ raw38670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38670step1 raw38670step1Labels raw38670step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw38671 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw38671Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38671step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw38671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38671 raw38671Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw38671 raw38671Labels = mixedMoment B raw38671step0 raw38671step0Labels := by
      have ha : raw38671step0 = raw38671 := by apply Matrix.ext; unfold raw38671step0 raw38671; decide +kernel
      have hl : raw38671Labels = labelEmbedding2 ∘ raw38671step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38671 raw38671Labels raw38671step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw38672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw38672Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38672step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38672step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38672step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38672 raw38672Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw38672 raw38672Labels = mixedMoment B raw38672step0 raw38672step0Labels := by
      have ha : raw38672step0 = (fun i j => raw38672 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38672step0 raw38672; decide +kernel
      have hl : raw38672step0Labels = raw38672Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38672 raw38672Labels permutation8 permutation7
    mixedMoment B raw38672step0 raw38672step0Labels = mixedMoment B raw38672step1 raw38672step1Labels := by
      have ha : raw38672step1 = -raw38672step0 := by apply Matrix.ext; change ∀ i j, raw38672step1 i j = -(raw38672step0 i j); unfold raw38672step1 raw38672step0; decide +kernel
      have hl : raw38672step1Labels = raw38672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38672step1 raw38672step1Labels = mixedMoment B raw38672step2 raw38672step2Labels := by
      have ha : raw38672step2 = raw38672step1 := by apply Matrix.ext; unfold raw38672step2 raw38672step1; decide +kernel
      have hl : raw38672step1Labels = labelEmbedding4 ∘ raw38672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38672step1 raw38672step1Labels raw38672step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw38673 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw38673Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38673step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw38673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38673 raw38673Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw38673 raw38673Labels = mixedMoment B raw38673step0 raw38673step0Labels := by
      have ha : raw38673step0 = raw38673 := by apply Matrix.ext; unfold raw38673step0 raw38673; decide +kernel
      have hl : raw38673Labels = labelEmbedding2 ∘ raw38673step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38673 raw38673Labels raw38673step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw38674 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw38674Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38674step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38674step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38674step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38674 raw38674Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw38674 raw38674Labels = mixedMoment B raw38674step0 raw38674step0Labels := by
      have ha : raw38674step0 = (fun i j => raw38674 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38674step0 raw38674; decide +kernel
      have hl : raw38674step0Labels = raw38674Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38674 raw38674Labels permutation8 permutation7
    mixedMoment B raw38674step0 raw38674step0Labels = mixedMoment B raw38674step1 raw38674step1Labels := by
      have ha : raw38674step1 = -raw38674step0 := by apply Matrix.ext; change ∀ i j, raw38674step1 i j = -(raw38674step0 i j); unfold raw38674step1 raw38674step0; decide +kernel
      have hl : raw38674step1Labels = raw38674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38674step1 raw38674step1Labels = mixedMoment B raw38674step2 raw38674step2Labels := by
      have ha : raw38674step2 = raw38674step1 := by apply Matrix.ext; unfold raw38674step2 raw38674step1; decide +kernel
      have hl : raw38674step1Labels = labelEmbedding4 ∘ raw38674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38674step1 raw38674step1Labels raw38674step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw38675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38675Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38675 raw38675Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw38675 raw38675Labels = mixedMoment B raw38675step0 raw38675step0Labels := by
      have ha : raw38675step0 = raw38675 := by apply Matrix.ext; unfold raw38675step0 raw38675; decide +kernel
      have hl : raw38675Labels = labelEmbedding2 ∘ raw38675step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38675 raw38675Labels raw38675step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw38676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38676Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38676step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38676step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38676 raw38676Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw38676 raw38676Labels = mixedMoment B raw38676step0 raw38676step0Labels := by
      have ha : raw38676step0 = (fun i j => raw38676 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38676step0 raw38676; decide +kernel
      have hl : raw38676step0Labels = raw38676Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38676 raw38676Labels permutation32 permutation7
    mixedMoment B raw38676step0 raw38676step0Labels = mixedMoment B raw38676step1 raw38676step1Labels := by
      have ha : raw38676step1 = -raw38676step0 := by apply Matrix.ext; change ∀ i j, raw38676step1 i j = -(raw38676step0 i j); unfold raw38676step1 raw38676step0; decide +kernel
      have hl : raw38676step1Labels = raw38676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38676step1 raw38676step1Labels = mixedMoment B raw38676step2 raw38676step2Labels := by
      have ha : raw38676step2 = raw38676step1 := by apply Matrix.ext; unfold raw38676step2 raw38676step1; decide +kernel
      have hl : raw38676step1Labels = labelEmbedding4 ∘ raw38676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38676step1 raw38676step1Labels raw38676step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw38677 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38677Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38677step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38677 raw38677Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw38677 raw38677Labels = mixedMoment B raw38677step0 raw38677step0Labels := by
      have ha : raw38677step0 = raw38677 := by apply Matrix.ext; unfold raw38677step0 raw38677; decide +kernel
      have hl : raw38677Labels = labelEmbedding2 ∘ raw38677step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38677 raw38677Labels raw38677step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw38678 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38678Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38678step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38678step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38678 raw38678Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw38678 raw38678Labels = mixedMoment B raw38678step0 raw38678step0Labels := by
      have ha : raw38678step0 = (fun i j => raw38678 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38678step0 raw38678; decide +kernel
      have hl : raw38678step0Labels = raw38678Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38678 raw38678Labels permutation8 permutation7
    mixedMoment B raw38678step0 raw38678step0Labels = mixedMoment B raw38678step1 raw38678step1Labels := by
      have ha : raw38678step1 = -raw38678step0 := by apply Matrix.ext; change ∀ i j, raw38678step1 i j = -(raw38678step0 i j); unfold raw38678step1 raw38678step0; decide +kernel
      have hl : raw38678step1Labels = raw38678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38678step1 raw38678step1Labels = mixedMoment B raw38678step2 raw38678step2Labels := by
      have ha : raw38678step2 = raw38678step1 := by apply Matrix.ext; unfold raw38678step2 raw38678step1; decide +kernel
      have hl : raw38678step1Labels = labelEmbedding4 ∘ raw38678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38678step1 raw38678step1Labels raw38678step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw38679 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw38679Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38679step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw38679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38679 raw38679Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw38679 raw38679Labels = mixedMoment B raw38679step0 raw38679step0Labels := by
      have ha : raw38679step0 = raw38679 := by apply Matrix.ext; unfold raw38679step0 raw38679; decide +kernel
      have hl : raw38679Labels = labelEmbedding2 ∘ raw38679step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38679 raw38679Labels raw38679step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw38680 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw38680Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38680step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw38680step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38680step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw38680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38680 raw38680Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw38680 raw38680Labels = mixedMoment B raw38680step0 raw38680step0Labels := by
      have ha : raw38680step0 = (fun i j => raw38680 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38680step0 raw38680; decide +kernel
      have hl : raw38680step0Labels = raw38680Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38680 raw38680Labels permutation7 permutation7
    mixedMoment B raw38680step0 raw38680step0Labels = mixedMoment B raw38680step1 raw38680step1Labels := by
      have ha : raw38680step1 = raw38680step0 := by apply Matrix.ext; unfold raw38680step1 raw38680step0; decide +kernel
      have hl : raw38680step0Labels = labelEmbedding4 ∘ raw38680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38680step0 raw38680step0Labels raw38680step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw38681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38681Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38681 raw38681Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw38681 raw38681Labels = mixedMoment B raw38681step0 raw38681step0Labels := by
      have ha : raw38681step0 = raw38681 := by apply Matrix.ext; unfold raw38681step0 raw38681; decide +kernel
      have hl : raw38681Labels = labelEmbedding2 ∘ raw38681step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38681 raw38681Labels raw38681step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw38682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38682Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38682step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38682step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38682 raw38682Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw38682 raw38682Labels = mixedMoment B raw38682step0 raw38682step0Labels := by
      have ha : raw38682step0 = (fun i j => raw38682 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38682step0 raw38682; decide +kernel
      have hl : raw38682step0Labels = raw38682Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38682 raw38682Labels permutation48 permutation5
    mixedMoment B raw38682step0 raw38682step0Labels = mixedMoment B raw38682step1 raw38682step1Labels := by
      have ha : raw38682step1 = -raw38682step0 := by apply Matrix.ext; change ∀ i j, raw38682step1 i j = -(raw38682step0 i j); unfold raw38682step1 raw38682step0; decide +kernel
      have hl : raw38682step1Labels = raw38682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38682step1 raw38682step1Labels = mixedMoment B raw38682step2 raw38682step2Labels := by
      have ha : raw38682step2 = raw38682step1 := by apply Matrix.ext; unfold raw38682step2 raw38682step1; decide +kernel
      have hl : raw38682step1Labels = labelEmbedding4 ∘ raw38682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38682step1 raw38682step1Labels raw38682step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

def raw38683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38683Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38683step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38683 raw38683Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw38683 raw38683Labels = mixedMoment B raw38683step0 raw38683step0Labels := by
      have ha : raw38683step0 = raw38683 := by apply Matrix.ext; unfold raw38683step0 raw38683; decide +kernel
      have hl : raw38683Labels = labelEmbedding2 ∘ raw38683step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38683 raw38683Labels raw38683step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw38684 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38684Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38684step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw38684step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw38684step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw38684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38684 raw38684Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw38684 raw38684Labels = mixedMoment B raw38684step0 raw38684step0Labels := by
      have ha : raw38684step0 = (fun i j => raw38684 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38684step0 raw38684; decide +kernel
      have hl : raw38684step0Labels = raw38684Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38684 raw38684Labels permutation8 permutation7
    mixedMoment B raw38684step0 raw38684step0Labels = mixedMoment B raw38684step1 raw38684step1Labels := by
      have ha : raw38684step1 = -raw38684step0 := by apply Matrix.ext; change ∀ i j, raw38684step1 i j = -(raw38684step0 i j); unfold raw38684step1 raw38684step0; decide +kernel
      have hl : raw38684step1Labels = raw38684step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38684step1 raw38684step1Labels = mixedMoment B raw38684step2 raw38684step2Labels := by
      have ha : raw38684step2 = raw38684step1 := by apply Matrix.ext; unfold raw38684step2 raw38684step1; decide +kernel
      have hl : raw38684step1Labels = labelEmbedding4 ∘ raw38684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38684step1 raw38684step1Labels raw38684step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3308 node3308Labels := by rfl

def raw38685 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38685Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38685step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38685 raw38685Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw38685 raw38685Labels = mixedMoment B raw38685step0 raw38685step0Labels := by
      have ha : raw38685step0 = raw38685 := by apply Matrix.ext; unfold raw38685step0 raw38685; decide +kernel
      have hl : raw38685Labels = labelEmbedding2 ∘ raw38685step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38685 raw38685Labels raw38685step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw38686 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38686Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38686step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38686step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38686step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38686 raw38686Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw38686 raw38686Labels = mixedMoment B raw38686step0 raw38686step0Labels := by
      have ha : raw38686step0 = (fun i j => raw38686 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38686step0 raw38686; decide +kernel
      have hl : raw38686step0Labels = raw38686Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38686 raw38686Labels permutation10 permutation5
    mixedMoment B raw38686step0 raw38686step0Labels = mixedMoment B raw38686step1 raw38686step1Labels := by
      have ha : raw38686step1 = -raw38686step0 := by apply Matrix.ext; change ∀ i j, raw38686step1 i j = -(raw38686step0 i j); unfold raw38686step1 raw38686step0; decide +kernel
      have hl : raw38686step1Labels = raw38686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38686step1 raw38686step1Labels = mixedMoment B raw38686step2 raw38686step2Labels := by
      have ha : raw38686step2 = raw38686step1 := by apply Matrix.ext; unfold raw38686step2 raw38686step1; decide +kernel
      have hl : raw38686step1Labels = labelEmbedding4 ∘ raw38686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38686step1 raw38686step1Labels raw38686step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3309 node3309Labels := by rfl

def raw38687 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw38687Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38687step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw38687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38687 raw38687Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw38687 raw38687Labels = mixedMoment B raw38687step0 raw38687step0Labels := by
      have ha : raw38687step0 = raw38687 := by apply Matrix.ext; unfold raw38687step0 raw38687; decide +kernel
      have hl : raw38687Labels = labelEmbedding2 ∘ raw38687step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38687 raw38687Labels raw38687step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw38688 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw38688Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38688step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw38688step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38688step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw38688step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38688step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw38688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38688 raw38688Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw38688 raw38688Labels = mixedMoment B raw38688step0 raw38688step0Labels := by
      have ha : raw38688step0 = (fun i j => raw38688 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38688step0 raw38688; decide +kernel
      have hl : raw38688step0Labels = raw38688Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38688 raw38688Labels permutation2 permutation7
    mixedMoment B raw38688step0 raw38688step0Labels = mixedMoment B raw38688step1 raw38688step1Labels := by
      have ha : raw38688step1 = -raw38688step0 := by apply Matrix.ext; change ∀ i j, raw38688step1 i j = -(raw38688step0 i j); unfold raw38688step1 raw38688step0; decide +kernel
      have hl : raw38688step1Labels = raw38688step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38688step1 raw38688step1Labels = mixedMoment B raw38688step2 raw38688step2Labels := by
      have ha : raw38688step2 = raw38688step1 := by apply Matrix.ext; unfold raw38688step2 raw38688step1; decide +kernel
      have hl : raw38688step1Labels = labelEmbedding4 ∘ raw38688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38688step1 raw38688step1Labels raw38688step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3310 node3310Labels := by rfl

def raw38689 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw38689Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38689step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw38689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38689 raw38689Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw38689 raw38689Labels = mixedMoment B raw38689step0 raw38689step0Labels := by
      have ha : raw38689step0 = raw38689 := by apply Matrix.ext; unfold raw38689step0 raw38689; decide +kernel
      have hl : raw38689Labels = labelEmbedding2 ∘ raw38689step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38689 raw38689Labels raw38689step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw38690 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw38690Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38690step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw38690step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38690step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw38690step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38690step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw38690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38690 raw38690Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw38690 raw38690Labels = mixedMoment B raw38690step0 raw38690step0Labels := by
      have ha : raw38690step0 = (fun i j => raw38690 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38690step0 raw38690; decide +kernel
      have hl : raw38690step0Labels = raw38690Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38690 raw38690Labels permutation3 permutation5
    mixedMoment B raw38690step0 raw38690step0Labels = mixedMoment B raw38690step1 raw38690step1Labels := by
      have ha : raw38690step1 = -raw38690step0 := by apply Matrix.ext; change ∀ i j, raw38690step1 i j = -(raw38690step0 i j); unfold raw38690step1 raw38690step0; decide +kernel
      have hl : raw38690step1Labels = raw38690step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38690step1 raw38690step1Labels = mixedMoment B raw38690step2 raw38690step2Labels := by
      have ha : raw38690step2 = raw38690step1 := by apply Matrix.ext; unfold raw38690step2 raw38690step1; decide +kernel
      have hl : raw38690step1Labels = labelEmbedding4 ∘ raw38690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38690step1 raw38690step1Labels raw38690step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3311 node3311Labels := by rfl

def raw38691 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw38691Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38691step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw38691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38691 raw38691Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw38691 raw38691Labels = mixedMoment B raw38691step0 raw38691step0Labels := by
      have ha : raw38691step0 = raw38691 := by apply Matrix.ext; unfold raw38691step0 raw38691; decide +kernel
      have hl : raw38691Labels = labelEmbedding2 ∘ raw38691step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38691 raw38691Labels raw38691step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw38692 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw38692Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38692step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw38692step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38692step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw38692step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38692step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw38692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38692 raw38692Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw38692 raw38692Labels = mixedMoment B raw38692step0 raw38692step0Labels := by
      have ha : raw38692step0 = (fun i j => raw38692 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38692step0 raw38692; decide +kernel
      have hl : raw38692step0Labels = raw38692Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38692 raw38692Labels permutation2 permutation5
    mixedMoment B raw38692step0 raw38692step0Labels = mixedMoment B raw38692step1 raw38692step1Labels := by
      have ha : raw38692step1 = -raw38692step0 := by apply Matrix.ext; change ∀ i j, raw38692step1 i j = -(raw38692step0 i j); unfold raw38692step1 raw38692step0; decide +kernel
      have hl : raw38692step1Labels = raw38692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38692step1 raw38692step1Labels = mixedMoment B raw38692step2 raw38692step2Labels := by
      have ha : raw38692step2 = raw38692step1 := by apply Matrix.ext; unfold raw38692step2 raw38692step1; decide +kernel
      have hl : raw38692step1Labels = labelEmbedding4 ∘ raw38692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38692step1 raw38692step1Labels raw38692step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3312 node3312Labels := by rfl

def raw38693 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw38693Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38693step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw38693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38693 raw38693Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw38693 raw38693Labels = mixedMoment B raw38693step0 raw38693step0Labels := by
      have ha : raw38693step0 = raw38693 := by apply Matrix.ext; unfold raw38693step0 raw38693; decide +kernel
      have hl : raw38693Labels = labelEmbedding2 ∘ raw38693step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38693 raw38693Labels raw38693step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw38694 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw38694Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38694step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw38694step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38694step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw38694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38694 raw38694Labels = mixedMoment B node3313 node3313Labels := by
  calc
    mixedMoment B raw38694 raw38694Labels = mixedMoment B raw38694step0 raw38694step0Labels := by
      have ha : raw38694step0 = (fun i j => raw38694 (permutation1 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38694step0 raw38694; decide +kernel
      have hl : raw38694step0Labels = raw38694Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38694 raw38694Labels permutation1 permutation5
    mixedMoment B raw38694step0 raw38694step0Labels = mixedMoment B raw38694step1 raw38694step1Labels := by
      have ha : raw38694step1 = raw38694step0 := by apply Matrix.ext; unfold raw38694step1 raw38694step0; decide +kernel
      have hl : raw38694step0Labels = labelEmbedding4 ∘ raw38694step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38694step0 raw38694step0Labels raw38694step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3313 node3313Labels := by rfl

def raw38695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38695Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38695 raw38695Labels = mixedMoment B node1759 node1759Labels := by
  calc
    mixedMoment B raw38695 raw38695Labels = mixedMoment B raw38695step0 raw38695step0Labels := by
      have ha : raw38695step0 = raw38695 := by apply Matrix.ext; unfold raw38695step0 raw38695; decide +kernel
      have hl : raw38695Labels = labelEmbedding2 ∘ raw38695step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38695 raw38695Labels raw38695step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1759 node1759Labels := by rfl

def raw38696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38696Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38696step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38696step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38696step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38696 raw38696Labels = mixedMoment B node1833 node1833Labels := by
  calc
    mixedMoment B raw38696 raw38696Labels = mixedMoment B raw38696step0 raw38696step0Labels := by
      have ha : raw38696step0 = (fun i j => raw38696 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38696step0 raw38696; decide +kernel
      have hl : raw38696step0Labels = raw38696Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38696 raw38696Labels permutation160 permutation7
    mixedMoment B raw38696step0 raw38696step0Labels = mixedMoment B raw38696step1 raw38696step1Labels := by
      have ha : raw38696step1 = -raw38696step0 := by apply Matrix.ext; change ∀ i j, raw38696step1 i j = -(raw38696step0 i j); unfold raw38696step1 raw38696step0; decide +kernel
      have hl : raw38696step1Labels = raw38696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38696step1 raw38696step1Labels = mixedMoment B raw38696step2 raw38696step2Labels := by
      have ha : raw38696step2 = raw38696step1 := by apply Matrix.ext; unfold raw38696step2 raw38696step1; decide +kernel
      have hl : raw38696step1Labels = labelEmbedding4 ∘ raw38696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38696step1 raw38696step1Labels raw38696step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1833 node1833Labels := by rfl

def raw38697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38697Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38697 raw38697Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw38697 raw38697Labels = mixedMoment B raw38697step0 raw38697step0Labels := by
      have ha : raw38697step0 = raw38697 := by apply Matrix.ext; unfold raw38697step0 raw38697; decide +kernel
      have hl : raw38697Labels = labelEmbedding2 ∘ raw38697step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38697 raw38697Labels raw38697step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1760 node1760Labels := by rfl

def raw38698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38698Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38698step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38698step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38698step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38698 raw38698Labels = mixedMoment B node1836 node1836Labels := by
  calc
    mixedMoment B raw38698 raw38698Labels = mixedMoment B raw38698step0 raw38698step0Labels := by
      have ha : raw38698step0 = (fun i j => raw38698 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38698step0 raw38698; decide +kernel
      have hl : raw38698step0Labels = raw38698Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38698 raw38698Labels permutation158 permutation7
    mixedMoment B raw38698step0 raw38698step0Labels = mixedMoment B raw38698step1 raw38698step1Labels := by
      have ha : raw38698step1 = -raw38698step0 := by apply Matrix.ext; change ∀ i j, raw38698step1 i j = -(raw38698step0 i j); unfold raw38698step1 raw38698step0; decide +kernel
      have hl : raw38698step1Labels = raw38698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38698step1 raw38698step1Labels = mixedMoment B raw38698step2 raw38698step2Labels := by
      have ha : raw38698step2 = raw38698step1 := by apply Matrix.ext; unfold raw38698step2 raw38698step1; decide +kernel
      have hl : raw38698step1Labels = labelEmbedding4 ∘ raw38698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38698step1 raw38698step1Labels raw38698step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1836 node1836Labels := by rfl

def raw38699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38699Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38699 raw38699Labels = mixedMoment B node1761 node1761Labels := by
  calc
    mixedMoment B raw38699 raw38699Labels = mixedMoment B raw38699step0 raw38699step0Labels := by
      have ha : raw38699step0 = raw38699 := by apply Matrix.ext; unfold raw38699step0 raw38699; decide +kernel
      have hl : raw38699Labels = labelEmbedding2 ∘ raw38699step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38699 raw38699Labels raw38699step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1761 node1761Labels := by rfl

def raw38700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38700Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38700step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38700step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38700step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38700 raw38700Labels = mixedMoment B node1837 node1837Labels := by
  calc
    mixedMoment B raw38700 raw38700Labels = mixedMoment B raw38700step0 raw38700step0Labels := by
      have ha : raw38700step0 = (fun i j => raw38700 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38700step0 raw38700; decide +kernel
      have hl : raw38700step0Labels = raw38700Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38700 raw38700Labels permutation158 permutation7
    mixedMoment B raw38700step0 raw38700step0Labels = mixedMoment B raw38700step1 raw38700step1Labels := by
      have ha : raw38700step1 = -raw38700step0 := by apply Matrix.ext; change ∀ i j, raw38700step1 i j = -(raw38700step0 i j); unfold raw38700step1 raw38700step0; decide +kernel
      have hl : raw38700step1Labels = raw38700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38700step1 raw38700step1Labels = mixedMoment B raw38700step2 raw38700step2Labels := by
      have ha : raw38700step2 = raw38700step1 := by apply Matrix.ext; unfold raw38700step2 raw38700step1; decide +kernel
      have hl : raw38700step1Labels = labelEmbedding4 ∘ raw38700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38700step1 raw38700step1Labels raw38700step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1837 node1837Labels := by rfl

def raw38701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38701Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38701 raw38701Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw38701 raw38701Labels = mixedMoment B raw38701step0 raw38701step0Labels := by
      have ha : raw38701step0 = raw38701 := by apply Matrix.ext; unfold raw38701step0 raw38701; decide +kernel
      have hl : raw38701Labels = labelEmbedding2 ∘ raw38701step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38701 raw38701Labels raw38701step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1762 node1762Labels := by rfl

def raw38702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38702Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38702step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38702step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38702 raw38702Labels = mixedMoment B node1847 node1847Labels := by
  calc
    mixedMoment B raw38702 raw38702Labels = mixedMoment B raw38702step0 raw38702step0Labels := by
      have ha : raw38702step0 = (fun i j => raw38702 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38702step0 raw38702; decide +kernel
      have hl : raw38702step0Labels = raw38702Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38702 raw38702Labels permutation152 permutation7
    mixedMoment B raw38702step0 raw38702step0Labels = mixedMoment B raw38702step1 raw38702step1Labels := by
      have ha : raw38702step1 = -raw38702step0 := by apply Matrix.ext; change ∀ i j, raw38702step1 i j = -(raw38702step0 i j); unfold raw38702step1 raw38702step0; decide +kernel
      have hl : raw38702step1Labels = raw38702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38702step1 raw38702step1Labels = mixedMoment B raw38702step2 raw38702step2Labels := by
      have ha : raw38702step2 = raw38702step1 := by apply Matrix.ext; unfold raw38702step2 raw38702step1; decide +kernel
      have hl : raw38702step1Labels = labelEmbedding4 ∘ raw38702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38702step1 raw38702step1Labels raw38702step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1847 node1847Labels := by rfl

def raw38703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38703Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38703 raw38703Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw38703 raw38703Labels = mixedMoment B raw38703step0 raw38703step0Labels := by
      have ha : raw38703step0 = raw38703 := by apply Matrix.ext; unfold raw38703step0 raw38703; decide +kernel
      have hl : raw38703Labels = labelEmbedding2 ∘ raw38703step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38703 raw38703Labels raw38703step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1763 node1763Labels := by rfl

def raw38704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38704Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38704step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38704step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38704 raw38704Labels = mixedMoment B node1842 node1842Labels := by
  calc
    mixedMoment B raw38704 raw38704Labels = mixedMoment B raw38704step0 raw38704step0Labels := by
      have ha : raw38704step0 = (fun i j => raw38704 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38704step0 raw38704; decide +kernel
      have hl : raw38704step0Labels = raw38704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38704 raw38704Labels permutation164 permutation7
    mixedMoment B raw38704step0 raw38704step0Labels = mixedMoment B raw38704step1 raw38704step1Labels := by
      have ha : raw38704step1 = -raw38704step0 := by apply Matrix.ext; change ∀ i j, raw38704step1 i j = -(raw38704step0 i j); unfold raw38704step1 raw38704step0; decide +kernel
      have hl : raw38704step1Labels = raw38704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38704step1 raw38704step1Labels = mixedMoment B raw38704step2 raw38704step2Labels := by
      have ha : raw38704step2 = raw38704step1 := by apply Matrix.ext; unfold raw38704step2 raw38704step1; decide +kernel
      have hl : raw38704step1Labels = labelEmbedding4 ∘ raw38704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38704step1 raw38704step1Labels raw38704step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1842 node1842Labels := by rfl

def raw38705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38705Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38705 raw38705Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw38705 raw38705Labels = mixedMoment B raw38705step0 raw38705step0Labels := by
      have ha : raw38705step0 = raw38705 := by apply Matrix.ext; unfold raw38705step0 raw38705; decide +kernel
      have hl : raw38705Labels = labelEmbedding2 ∘ raw38705step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38705 raw38705Labels raw38705step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1764 node1764Labels := by rfl

def raw38706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38706Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38706step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38706step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38706 raw38706Labels = mixedMoment B node1848 node1848Labels := by
  calc
    mixedMoment B raw38706 raw38706Labels = mixedMoment B raw38706step0 raw38706step0Labels := by
      have ha : raw38706step0 = (fun i j => raw38706 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38706step0 raw38706; decide +kernel
      have hl : raw38706step0Labels = raw38706Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38706 raw38706Labels permutation152 permutation7
    mixedMoment B raw38706step0 raw38706step0Labels = mixedMoment B raw38706step1 raw38706step1Labels := by
      have ha : raw38706step1 = -raw38706step0 := by apply Matrix.ext; change ∀ i j, raw38706step1 i j = -(raw38706step0 i j); unfold raw38706step1 raw38706step0; decide +kernel
      have hl : raw38706step1Labels = raw38706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38706step1 raw38706step1Labels = mixedMoment B raw38706step2 raw38706step2Labels := by
      have ha : raw38706step2 = raw38706step1 := by apply Matrix.ext; unfold raw38706step2 raw38706step1; decide +kernel
      have hl : raw38706step1Labels = labelEmbedding4 ∘ raw38706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38706step1 raw38706step1Labels raw38706step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1848 node1848Labels := by rfl

def raw38707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38707Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38707 raw38707Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw38707 raw38707Labels = mixedMoment B raw38707step0 raw38707step0Labels := by
      have ha : raw38707step0 = raw38707 := by apply Matrix.ext; unfold raw38707step0 raw38707; decide +kernel
      have hl : raw38707Labels = labelEmbedding2 ∘ raw38707step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38707 raw38707Labels raw38707step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1765 node1765Labels := by rfl

def raw38708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38708Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw38708step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38708step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38708 raw38708Labels = mixedMoment B node1843 node1843Labels := by
  calc
    mixedMoment B raw38708 raw38708Labels = mixedMoment B raw38708step0 raw38708step0Labels := by
      have ha : raw38708step0 = (fun i j => raw38708 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38708step0 raw38708; decide +kernel
      have hl : raw38708step0Labels = raw38708Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38708 raw38708Labels permutation34 permutation7
    mixedMoment B raw38708step0 raw38708step0Labels = mixedMoment B raw38708step1 raw38708step1Labels := by
      have ha : raw38708step1 = -raw38708step0 := by apply Matrix.ext; change ∀ i j, raw38708step1 i j = -(raw38708step0 i j); unfold raw38708step1 raw38708step0; decide +kernel
      have hl : raw38708step1Labels = raw38708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38708step1 raw38708step1Labels = mixedMoment B raw38708step2 raw38708step2Labels := by
      have ha : raw38708step2 = raw38708step1 := by apply Matrix.ext; unfold raw38708step2 raw38708step1; decide +kernel
      have hl : raw38708step1Labels = labelEmbedding4 ∘ raw38708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38708step1 raw38708step1Labels raw38708step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1843 node1843Labels := by rfl

def raw38709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38709Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38709 raw38709Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw38709 raw38709Labels = mixedMoment B raw38709step0 raw38709step0Labels := by
      have ha : raw38709step0 = raw38709 := by apply Matrix.ext; unfold raw38709step0 raw38709; decide +kernel
      have hl : raw38709Labels = labelEmbedding2 ∘ raw38709step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38709 raw38709Labels raw38709step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw38710 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38710Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38710step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38710step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38710 raw38710Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw38710 raw38710Labels = mixedMoment B raw38710step0 raw38710step0Labels := by
      have ha : raw38710step0 = (fun i j => raw38710 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38710step0 raw38710; decide +kernel
      have hl : raw38710step0Labels = raw38710Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38710 raw38710Labels permutation32 permutation7
    mixedMoment B raw38710step0 raw38710step0Labels = mixedMoment B raw38710step1 raw38710step1Labels := by
      have ha : raw38710step1 = -raw38710step0 := by apply Matrix.ext; change ∀ i j, raw38710step1 i j = -(raw38710step0 i j); unfold raw38710step1 raw38710step0; decide +kernel
      have hl : raw38710step1Labels = raw38710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38710step1 raw38710step1Labels = mixedMoment B raw38710step2 raw38710step2Labels := by
      have ha : raw38710step2 = raw38710step1 := by apply Matrix.ext; unfold raw38710step2 raw38710step1; decide +kernel
      have hl : raw38710step1Labels = labelEmbedding4 ∘ raw38710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38710step1 raw38710step1Labels raw38710step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

def raw38711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38711Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38711 raw38711Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw38711 raw38711Labels = mixedMoment B raw38711step0 raw38711step0Labels := by
      have ha : raw38711step0 = raw38711 := by apply Matrix.ext; unfold raw38711step0 raw38711; decide +kernel
      have hl : raw38711Labels = labelEmbedding2 ∘ raw38711step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38711 raw38711Labels raw38711step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1767 node1767Labels := by rfl

def raw38712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38712Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38712step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38712step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38712 raw38712Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw38712 raw38712Labels = mixedMoment B raw38712step0 raw38712step0Labels := by
      have ha : raw38712step0 = (fun i j => raw38712 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38712step0 raw38712; decide +kernel
      have hl : raw38712step0Labels = raw38712Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38712 raw38712Labels permutation33 permutation7
    mixedMoment B raw38712step0 raw38712step0Labels = mixedMoment B raw38712step1 raw38712step1Labels := by
      have ha : raw38712step1 = -raw38712step0 := by apply Matrix.ext; change ∀ i j, raw38712step1 i j = -(raw38712step0 i j); unfold raw38712step1 raw38712step0; decide +kernel
      have hl : raw38712step1Labels = raw38712step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38712step1 raw38712step1Labels = mixedMoment B raw38712step2 raw38712step2Labels := by
      have ha : raw38712step2 = raw38712step1 := by apply Matrix.ext; unfold raw38712step2 raw38712step1; decide +kernel
      have hl : raw38712step1Labels = labelEmbedding4 ∘ raw38712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38712step1 raw38712step1Labels raw38712step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

def raw38713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38713Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38713 raw38713Labels = mixedMoment B node1768 node1768Labels := by
  calc
    mixedMoment B raw38713 raw38713Labels = mixedMoment B raw38713step0 raw38713step0Labels := by
      have ha : raw38713step0 = raw38713 := by apply Matrix.ext; unfold raw38713step0 raw38713; decide +kernel
      have hl : raw38713Labels = labelEmbedding2 ∘ raw38713step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38713 raw38713Labels raw38713step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1768 node1768Labels := by rfl

def raw38714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38714Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38714step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38714step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38714step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38714 raw38714Labels = mixedMoment B node1834 node1834Labels := by
  calc
    mixedMoment B raw38714 raw38714Labels = mixedMoment B raw38714step0 raw38714step0Labels := by
      have ha : raw38714step0 = (fun i j => raw38714 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38714step0 raw38714; decide +kernel
      have hl : raw38714step0Labels = raw38714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38714 raw38714Labels permutation152 permutation7
    mixedMoment B raw38714step0 raw38714step0Labels = mixedMoment B raw38714step1 raw38714step1Labels := by
      have ha : raw38714step1 = -raw38714step0 := by apply Matrix.ext; change ∀ i j, raw38714step1 i j = -(raw38714step0 i j); unfold raw38714step1 raw38714step0; decide +kernel
      have hl : raw38714step1Labels = raw38714step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38714step1 raw38714step1Labels = mixedMoment B raw38714step2 raw38714step2Labels := by
      have ha : raw38714step2 = raw38714step1 := by apply Matrix.ext; unfold raw38714step2 raw38714step1; decide +kernel
      have hl : raw38714step1Labels = labelEmbedding4 ∘ raw38714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38714step1 raw38714step1Labels raw38714step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1834 node1834Labels := by rfl

def raw38715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38715Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38715 raw38715Labels = mixedMoment B node1769 node1769Labels := by
  calc
    mixedMoment B raw38715 raw38715Labels = mixedMoment B raw38715step0 raw38715step0Labels := by
      have ha : raw38715step0 = raw38715 := by apply Matrix.ext; unfold raw38715step0 raw38715; decide +kernel
      have hl : raw38715Labels = labelEmbedding2 ∘ raw38715step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38715 raw38715Labels raw38715step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1769 node1769Labels := by rfl

def raw38716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38716Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38716step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38716step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38716 raw38716Labels = mixedMoment B node1835 node1835Labels := by
  calc
    mixedMoment B raw38716 raw38716Labels = mixedMoment B raw38716step0 raw38716step0Labels := by
      have ha : raw38716step0 = (fun i j => raw38716 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38716step0 raw38716; decide +kernel
      have hl : raw38716step0Labels = raw38716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38716 raw38716Labels permutation152 permutation7
    mixedMoment B raw38716step0 raw38716step0Labels = mixedMoment B raw38716step1 raw38716step1Labels := by
      have ha : raw38716step1 = -raw38716step0 := by apply Matrix.ext; change ∀ i j, raw38716step1 i j = -(raw38716step0 i j); unfold raw38716step1 raw38716step0; decide +kernel
      have hl : raw38716step1Labels = raw38716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38716step1 raw38716step1Labels = mixedMoment B raw38716step2 raw38716step2Labels := by
      have ha : raw38716step2 = raw38716step1 := by apply Matrix.ext; unfold raw38716step2 raw38716step1; decide +kernel
      have hl : raw38716step1Labels = labelEmbedding4 ∘ raw38716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38716step1 raw38716step1Labels raw38716step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1835 node1835Labels := by rfl

def raw38717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38717Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38717 raw38717Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw38717 raw38717Labels = mixedMoment B raw38717step0 raw38717step0Labels := by
      have ha : raw38717step0 = raw38717 := by apply Matrix.ext; unfold raw38717step0 raw38717; decide +kernel
      have hl : raw38717Labels = labelEmbedding2 ∘ raw38717step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38717 raw38717Labels raw38717step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1771 node1771Labels := by rfl

def raw38718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38718Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38718step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38718step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38718 raw38718Labels = mixedMoment B node1838 node1838Labels := by
  calc
    mixedMoment B raw38718 raw38718Labels = mixedMoment B raw38718step0 raw38718step0Labels := by
      have ha : raw38718step0 = (fun i j => raw38718 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38718step0 raw38718; decide +kernel
      have hl : raw38718step0Labels = raw38718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38718 raw38718Labels permutation153 permutation7
    mixedMoment B raw38718step0 raw38718step0Labels = mixedMoment B raw38718step1 raw38718step1Labels := by
      have ha : raw38718step1 = -raw38718step0 := by apply Matrix.ext; change ∀ i j, raw38718step1 i j = -(raw38718step0 i j); unfold raw38718step1 raw38718step0; decide +kernel
      have hl : raw38718step1Labels = raw38718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38718step1 raw38718step1Labels = mixedMoment B raw38718step2 raw38718step2Labels := by
      have ha : raw38718step2 = raw38718step1 := by apply Matrix.ext; unfold raw38718step2 raw38718step1; decide +kernel
      have hl : raw38718step1Labels = labelEmbedding4 ∘ raw38718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38718step1 raw38718step1Labels raw38718step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1838 node1838Labels := by rfl

def raw38719 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38719Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38719 raw38719Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw38719 raw38719Labels = mixedMoment B raw38719step0 raw38719step0Labels := by
      have ha : raw38719step0 = raw38719 := by apply Matrix.ext; unfold raw38719step0 raw38719; decide +kernel
      have hl : raw38719Labels = labelEmbedding2 ∘ raw38719step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38719 raw38719Labels raw38719step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw38720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38720Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38720step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38720step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38720 raw38720Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw38720 raw38720Labels = mixedMoment B raw38720step0 raw38720step0Labels := by
      have ha : raw38720step0 = (fun i j => raw38720 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38720step0 raw38720; decide +kernel
      have hl : raw38720step0Labels = raw38720Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38720 raw38720Labels permutation32 permutation7
    mixedMoment B raw38720step0 raw38720step0Labels = mixedMoment B raw38720step1 raw38720step1Labels := by
      have ha : raw38720step1 = -raw38720step0 := by apply Matrix.ext; change ∀ i j, raw38720step1 i j = -(raw38720step0 i j); unfold raw38720step1 raw38720step0; decide +kernel
      have hl : raw38720step1Labels = raw38720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38720step1 raw38720step1Labels = mixedMoment B raw38720step2 raw38720step2Labels := by
      have ha : raw38720step2 = raw38720step1 := by apply Matrix.ext; unfold raw38720step2 raw38720step1; decide +kernel
      have hl : raw38720step1Labels = labelEmbedding4 ∘ raw38720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38720step1 raw38720step1Labels raw38720step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

def raw38721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38721Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38721 raw38721Labels = mixedMoment B node1774 node1774Labels := by
  calc
    mixedMoment B raw38721 raw38721Labels = mixedMoment B raw38721step0 raw38721step0Labels := by
      have ha : raw38721step0 = raw38721 := by apply Matrix.ext; unfold raw38721step0 raw38721; decide +kernel
      have hl : raw38721Labels = labelEmbedding2 ∘ raw38721step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38721 raw38721Labels raw38721step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1774 node1774Labels := by rfl

def raw38722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38722Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw38722step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38722step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38722 raw38722Labels = mixedMoment B node1840 node1840Labels := by
  calc
    mixedMoment B raw38722 raw38722Labels = mixedMoment B raw38722step0 raw38722step0Labels := by
      have ha : raw38722step0 = (fun i j => raw38722 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38722step0 raw38722; decide +kernel
      have hl : raw38722step0Labels = raw38722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38722 raw38722Labels permutation32 permutation7
    mixedMoment B raw38722step0 raw38722step0Labels = mixedMoment B raw38722step1 raw38722step1Labels := by
      have ha : raw38722step1 = -raw38722step0 := by apply Matrix.ext; change ∀ i j, raw38722step1 i j = -(raw38722step0 i j); unfold raw38722step1 raw38722step0; decide +kernel
      have hl : raw38722step1Labels = raw38722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38722step1 raw38722step1Labels = mixedMoment B raw38722step2 raw38722step2Labels := by
      have ha : raw38722step2 = raw38722step1 := by apply Matrix.ext; unfold raw38722step2 raw38722step1; decide +kernel
      have hl : raw38722step1Labels = labelEmbedding4 ∘ raw38722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38722step1 raw38722step1Labels raw38722step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1840 node1840Labels := by rfl

def raw38723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38723Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38723 raw38723Labels = mixedMoment B node1776 node1776Labels := by
  calc
    mixedMoment B raw38723 raw38723Labels = mixedMoment B raw38723step0 raw38723step0Labels := by
      have ha : raw38723step0 = raw38723 := by apply Matrix.ext; unfold raw38723step0 raw38723; decide +kernel
      have hl : raw38723Labels = labelEmbedding2 ∘ raw38723step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38723 raw38723Labels raw38723step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1776 node1776Labels := by rfl

def raw38724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38724Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38724step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38724step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38724step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38724 raw38724Labels = mixedMoment B node1844 node1844Labels := by
  calc
    mixedMoment B raw38724 raw38724Labels = mixedMoment B raw38724step0 raw38724step0Labels := by
      have ha : raw38724step0 = (fun i j => raw38724 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38724step0 raw38724; decide +kernel
      have hl : raw38724step0Labels = raw38724Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38724 raw38724Labels permutation170 permutation7
    mixedMoment B raw38724step0 raw38724step0Labels = mixedMoment B raw38724step1 raw38724step1Labels := by
      have ha : raw38724step1 = -raw38724step0 := by apply Matrix.ext; change ∀ i j, raw38724step1 i j = -(raw38724step0 i j); unfold raw38724step1 raw38724step0; decide +kernel
      have hl : raw38724step1Labels = raw38724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38724step1 raw38724step1Labels = mixedMoment B raw38724step2 raw38724step2Labels := by
      have ha : raw38724step2 = raw38724step1 := by apply Matrix.ext; unfold raw38724step2 raw38724step1; decide +kernel
      have hl : raw38724step1Labels = labelEmbedding4 ∘ raw38724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38724step1 raw38724step1Labels raw38724step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1844 node1844Labels := by rfl

def raw38725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38725Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38725 raw38725Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw38725 raw38725Labels = mixedMoment B raw38725step0 raw38725step0Labels := by
      have ha : raw38725step0 = raw38725 := by apply Matrix.ext; unfold raw38725step0 raw38725; decide +kernel
      have hl : raw38725Labels = labelEmbedding2 ∘ raw38725step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38725 raw38725Labels raw38725step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw38726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38726Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38726step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38726step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38726 raw38726Labels = mixedMoment B node1854 node1854Labels := by
  calc
    mixedMoment B raw38726 raw38726Labels = mixedMoment B raw38726step0 raw38726step0Labels := by
      have ha : raw38726step0 = (fun i j => raw38726 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38726step0 raw38726; decide +kernel
      have hl : raw38726step0Labels = raw38726Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38726 raw38726Labels permutation33 permutation7
    mixedMoment B raw38726step0 raw38726step0Labels = mixedMoment B raw38726step1 raw38726step1Labels := by
      have ha : raw38726step1 = -raw38726step0 := by apply Matrix.ext; change ∀ i j, raw38726step1 i j = -(raw38726step0 i j); unfold raw38726step1 raw38726step0; decide +kernel
      have hl : raw38726step1Labels = raw38726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38726step1 raw38726step1Labels = mixedMoment B raw38726step2 raw38726step2Labels := by
      have ha : raw38726step2 = raw38726step1 := by apply Matrix.ext; unfold raw38726step2 raw38726step1; decide +kernel
      have hl : raw38726step1Labels = labelEmbedding4 ∘ raw38726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38726step1 raw38726step1Labels raw38726step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1854 node1854Labels := by rfl

def raw38727 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38727Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38727 raw38727Labels = mixedMoment B node1779 node1779Labels := by
  calc
    mixedMoment B raw38727 raw38727Labels = mixedMoment B raw38727step0 raw38727step0Labels := by
      have ha : raw38727step0 = raw38727 := by apply Matrix.ext; unfold raw38727step0 raw38727; decide +kernel
      have hl : raw38727Labels = labelEmbedding2 ∘ raw38727step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38727 raw38727Labels raw38727step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1779 node1779Labels := by rfl

def raw38728 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38728Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw38728step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38728step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38728 raw38728Labels = mixedMoment B node1845 node1845Labels := by
  calc
    mixedMoment B raw38728 raw38728Labels = mixedMoment B raw38728step0 raw38728step0Labels := by
      have ha : raw38728step0 = (fun i j => raw38728 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38728step0 raw38728; decide +kernel
      have hl : raw38728step0Labels = raw38728Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38728 raw38728Labels permutation34 permutation7
    mixedMoment B raw38728step0 raw38728step0Labels = mixedMoment B raw38728step1 raw38728step1Labels := by
      have ha : raw38728step1 = -raw38728step0 := by apply Matrix.ext; change ∀ i j, raw38728step1 i j = -(raw38728step0 i j); unfold raw38728step1 raw38728step0; decide +kernel
      have hl : raw38728step1Labels = raw38728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38728step1 raw38728step1Labels = mixedMoment B raw38728step2 raw38728step2Labels := by
      have ha : raw38728step2 = raw38728step1 := by apply Matrix.ext; unfold raw38728step2 raw38728step1; decide +kernel
      have hl : raw38728step1Labels = labelEmbedding4 ∘ raw38728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38728step1 raw38728step1Labels raw38728step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1845 node1845Labels := by rfl

def raw38729 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38729Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38729 raw38729Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw38729 raw38729Labels = mixedMoment B raw38729step0 raw38729step0Labels := by
      have ha : raw38729step0 = raw38729 := by apply Matrix.ext; unfold raw38729step0 raw38729; decide +kernel
      have hl : raw38729Labels = labelEmbedding2 ∘ raw38729step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38729 raw38729Labels raw38729step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw38730 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38730Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38730step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38730step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38730 raw38730Labels = mixedMoment B node1846 node1846Labels := by
  calc
    mixedMoment B raw38730 raw38730Labels = mixedMoment B raw38730step0 raw38730step0Labels := by
      have ha : raw38730step0 = (fun i j => raw38730 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38730step0 raw38730; decide +kernel
      have hl : raw38730step0Labels = raw38730Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38730 raw38730Labels permutation34 permutation7
    mixedMoment B raw38730step0 raw38730step0Labels = mixedMoment B raw38730step1 raw38730step1Labels := by
      have ha : raw38730step1 = -raw38730step0 := by apply Matrix.ext; change ∀ i j, raw38730step1 i j = -(raw38730step0 i j); unfold raw38730step1 raw38730step0; decide +kernel
      have hl : raw38730step1Labels = raw38730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38730step1 raw38730step1Labels = mixedMoment B raw38730step2 raw38730step2Labels := by
      have ha : raw38730step2 = raw38730step1 := by apply Matrix.ext; unfold raw38730step2 raw38730step1; decide +kernel
      have hl : raw38730step1Labels = labelEmbedding4 ∘ raw38730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38730step1 raw38730step1Labels raw38730step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1846 node1846Labels := by rfl

def raw38731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38731Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38731 raw38731Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw38731 raw38731Labels = mixedMoment B raw38731step0 raw38731step0Labels := by
      have ha : raw38731step0 = raw38731 := by apply Matrix.ext; unfold raw38731step0 raw38731; decide +kernel
      have hl : raw38731Labels = labelEmbedding2 ∘ raw38731step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38731 raw38731Labels raw38731step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw38732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38732Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38732step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38732step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38732 raw38732Labels = mixedMoment B node1855 node1855Labels := by
  calc
    mixedMoment B raw38732 raw38732Labels = mixedMoment B raw38732step0 raw38732step0Labels := by
      have ha : raw38732step0 = (fun i j => raw38732 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38732step0 raw38732; decide +kernel
      have hl : raw38732step0Labels = raw38732Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38732 raw38732Labels permutation35 permutation7
    mixedMoment B raw38732step0 raw38732step0Labels = mixedMoment B raw38732step1 raw38732step1Labels := by
      have ha : raw38732step1 = -raw38732step0 := by apply Matrix.ext; change ∀ i j, raw38732step1 i j = -(raw38732step0 i j); unfold raw38732step1 raw38732step0; decide +kernel
      have hl : raw38732step1Labels = raw38732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38732step1 raw38732step1Labels = mixedMoment B raw38732step2 raw38732step2Labels := by
      have ha : raw38732step2 = raw38732step1 := by apply Matrix.ext; unfold raw38732step2 raw38732step1; decide +kernel
      have hl : raw38732step1Labels = labelEmbedding4 ∘ raw38732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38732step1 raw38732step1Labels raw38732step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1855 node1855Labels := by rfl

def raw38733 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38733Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38733step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38733 raw38733Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw38733 raw38733Labels = mixedMoment B raw38733step0 raw38733step0Labels := by
      have ha : raw38733step0 = raw38733 := by apply Matrix.ext; unfold raw38733step0 raw38733; decide +kernel
      have hl : raw38733Labels = labelEmbedding2 ∘ raw38733step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38733 raw38733Labels raw38733step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1783 node1783Labels := by rfl

def raw38734 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38734Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38734step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -2, 3], ![-3, 1, 2]]
def raw38734step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw38734step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw38734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38734 raw38734Labels = mixedMoment B node1857 node1857Labels := by
  calc
    mixedMoment B raw38734 raw38734Labels = mixedMoment B raw38734step0 raw38734step0Labels := by
      have ha : raw38734step0 = (fun i j => raw38734 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38734step0 raw38734; decide +kernel
      have hl : raw38734step0Labels = raw38734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38734 raw38734Labels permutation9 permutation7
    mixedMoment B raw38734step0 raw38734step0Labels = mixedMoment B raw38734step1 raw38734step1Labels := by
      have ha : raw38734step1 = -raw38734step0 := by apply Matrix.ext; change ∀ i j, raw38734step1 i j = -(raw38734step0 i j); unfold raw38734step1 raw38734step0; decide +kernel
      have hl : raw38734step1Labels = raw38734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38734step1 raw38734step1Labels = mixedMoment B raw38734step2 raw38734step2Labels := by
      have ha : raw38734step2 = raw38734step1 := by apply Matrix.ext; unfold raw38734step2 raw38734step1; decide +kernel
      have hl : raw38734step1Labels = labelEmbedding4 ∘ raw38734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38734step1 raw38734step1Labels raw38734step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1857 node1857Labels := by rfl

def raw38735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38735Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38735 raw38735Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw38735 raw38735Labels = mixedMoment B raw38735step0 raw38735step0Labels := by
      have ha : raw38735step0 = raw38735 := by apply Matrix.ext; unfold raw38735step0 raw38735; decide +kernel
      have hl : raw38735Labels = labelEmbedding2 ∘ raw38735step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38735 raw38735Labels raw38735step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1784 node1784Labels := by rfl

def raw38736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38736Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38736step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38736 raw38736Labels = mixedMoment B node1884 node1884Labels := by
  calc
    mixedMoment B raw38736 raw38736Labels = mixedMoment B raw38736step0 raw38736step0Labels := by
      have ha : raw38736step0 = (fun i j => raw38736 (permutation686 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38736step0 raw38736; decide +kernel
      have hl : raw38736step0Labels = raw38736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38736 raw38736Labels permutation686 permutation7
    mixedMoment B raw38736step0 raw38736step0Labels = mixedMoment B raw38736step1 raw38736step1Labels := by
      have ha : raw38736step1 = raw38736step0 := by apply Matrix.ext; unfold raw38736step1 raw38736step0; decide +kernel
      have hl : raw38736step0Labels = labelEmbedding4 ∘ raw38736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38736step0 raw38736step0Labels raw38736step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1884 node1884Labels := by rfl

def raw38737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38737Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38737 raw38737Labels = mixedMoment B node1785 node1785Labels := by
  calc
    mixedMoment B raw38737 raw38737Labels = mixedMoment B raw38737step0 raw38737step0Labels := by
      have ha : raw38737step0 = raw38737 := by apply Matrix.ext; unfold raw38737step0 raw38737; decide +kernel
      have hl : raw38737Labels = labelEmbedding2 ∘ raw38737step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38737 raw38737Labels raw38737step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1785 node1785Labels := by rfl

def raw38738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38738Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38738step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38738step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38738 raw38738Labels = mixedMoment B node1981 node1981Labels := by
  calc
    mixedMoment B raw38738 raw38738Labels = mixedMoment B raw38738step0 raw38738step0Labels := by
      have ha : raw38738step0 = (fun i j => raw38738 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38738step0 raw38738; decide +kernel
      have hl : raw38738step0Labels = raw38738Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38738 raw38738Labels permutation176 permutation7
    mixedMoment B raw38738step0 raw38738step0Labels = mixedMoment B raw38738step1 raw38738step1Labels := by
      have ha : raw38738step1 = -raw38738step0 := by apply Matrix.ext; change ∀ i j, raw38738step1 i j = -(raw38738step0 i j); unfold raw38738step1 raw38738step0; decide +kernel
      have hl : raw38738step1Labels = raw38738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38738step1 raw38738step1Labels = mixedMoment B raw38738step2 raw38738step2Labels := by
      have ha : raw38738step2 = raw38738step1 := by apply Matrix.ext; unfold raw38738step2 raw38738step1; decide +kernel
      have hl : raw38738step1Labels = labelEmbedding4 ∘ raw38738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38738step1 raw38738step1Labels raw38738step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1981 node1981Labels := by rfl

def raw38739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38739Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38739 raw38739Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw38739 raw38739Labels = mixedMoment B raw38739step0 raw38739step0Labels := by
      have ha : raw38739step0 = raw38739 := by apply Matrix.ext; unfold raw38739step0 raw38739; decide +kernel
      have hl : raw38739Labels = labelEmbedding2 ∘ raw38739step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38739 raw38739Labels raw38739step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1786 node1786Labels := by rfl

def raw38740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38740Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38740step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38740step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38740 raw38740Labels = mixedMoment B node1982 node1982Labels := by
  calc
    mixedMoment B raw38740 raw38740Labels = mixedMoment B raw38740step0 raw38740step0Labels := by
      have ha : raw38740step0 = (fun i j => raw38740 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38740step0 raw38740; decide +kernel
      have hl : raw38740step0Labels = raw38740Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38740 raw38740Labels permutation176 permutation7
    mixedMoment B raw38740step0 raw38740step0Labels = mixedMoment B raw38740step1 raw38740step1Labels := by
      have ha : raw38740step1 = -raw38740step0 := by apply Matrix.ext; change ∀ i j, raw38740step1 i j = -(raw38740step0 i j); unfold raw38740step1 raw38740step0; decide +kernel
      have hl : raw38740step1Labels = raw38740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38740step1 raw38740step1Labels = mixedMoment B raw38740step2 raw38740step2Labels := by
      have ha : raw38740step2 = raw38740step1 := by apply Matrix.ext; unfold raw38740step2 raw38740step1; decide +kernel
      have hl : raw38740step1Labels = labelEmbedding4 ∘ raw38740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38740step1 raw38740step1Labels raw38740step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1982 node1982Labels := by rfl

def raw38741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38741Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38741 raw38741Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw38741 raw38741Labels = mixedMoment B raw38741step0 raw38741step0Labels := by
      have ha : raw38741step0 = raw38741 := by apply Matrix.ext; unfold raw38741step0 raw38741; decide +kernel
      have hl : raw38741Labels = labelEmbedding2 ∘ raw38741step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38741 raw38741Labels raw38741step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw38742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38742Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38742step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38742step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38742 raw38742Labels = mixedMoment B node1983 node1983Labels := by
  calc
    mixedMoment B raw38742 raw38742Labels = mixedMoment B raw38742step0 raw38742step0Labels := by
      have ha : raw38742step0 = (fun i j => raw38742 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38742step0 raw38742; decide +kernel
      have hl : raw38742step0Labels = raw38742Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38742 raw38742Labels permutation176 permutation7
    mixedMoment B raw38742step0 raw38742step0Labels = mixedMoment B raw38742step1 raw38742step1Labels := by
      have ha : raw38742step1 = -raw38742step0 := by apply Matrix.ext; change ∀ i j, raw38742step1 i j = -(raw38742step0 i j); unfold raw38742step1 raw38742step0; decide +kernel
      have hl : raw38742step1Labels = raw38742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38742step1 raw38742step1Labels = mixedMoment B raw38742step2 raw38742step2Labels := by
      have ha : raw38742step2 = raw38742step1 := by apply Matrix.ext; unfold raw38742step2 raw38742step1; decide +kernel
      have hl : raw38742step1Labels = labelEmbedding4 ∘ raw38742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38742step1 raw38742step1Labels raw38742step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1983 node1983Labels := by rfl

def raw38743 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38743Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38743 raw38743Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw38743 raw38743Labels = mixedMoment B raw38743step0 raw38743step0Labels := by
      have ha : raw38743step0 = raw38743 := by apply Matrix.ext; unfold raw38743step0 raw38743; decide +kernel
      have hl : raw38743Labels = labelEmbedding2 ∘ raw38743step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38743 raw38743Labels raw38743step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw38744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38744Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, -1, 3]]
def raw38744step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38744step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38744 raw38744Labels = mixedMoment B node1984 node1984Labels := by
  calc
    mixedMoment B raw38744 raw38744Labels = mixedMoment B raw38744step0 raw38744step0Labels := by
      have ha : raw38744step0 = (fun i j => raw38744 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38744step0 raw38744; decide +kernel
      have hl : raw38744step0Labels = raw38744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38744 raw38744Labels permutation38 permutation7
    mixedMoment B raw38744step0 raw38744step0Labels = mixedMoment B raw38744step1 raw38744step1Labels := by
      have ha : raw38744step1 = -raw38744step0 := by apply Matrix.ext; change ∀ i j, raw38744step1 i j = -(raw38744step0 i j); unfold raw38744step1 raw38744step0; decide +kernel
      have hl : raw38744step1Labels = raw38744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38744step1 raw38744step1Labels = mixedMoment B raw38744step2 raw38744step2Labels := by
      have ha : raw38744step2 = raw38744step1 := by apply Matrix.ext; unfold raw38744step2 raw38744step1; decide +kernel
      have hl : raw38744step1Labels = labelEmbedding4 ∘ raw38744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38744step1 raw38744step1Labels raw38744step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1984 node1984Labels := by rfl

def raw38745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38745Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38745 raw38745Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw38745 raw38745Labels = mixedMoment B raw38745step0 raw38745step0Labels := by
      have ha : raw38745step0 = raw38745 := by apply Matrix.ext; unfold raw38745step0 raw38745; decide +kernel
      have hl : raw38745Labels = labelEmbedding2 ∘ raw38745step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38745 raw38745Labels raw38745step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1798 node1798Labels := by rfl

def raw38746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38746Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38746step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38746step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38746 raw38746Labels = mixedMoment B node2067 node2067Labels := by
  calc
    mixedMoment B raw38746 raw38746Labels = mixedMoment B raw38746step0 raw38746step0Labels := by
      have ha : raw38746step0 = (fun i j => raw38746 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38746step0 raw38746; decide +kernel
      have hl : raw38746step0Labels = raw38746Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38746 raw38746Labels permutation176 permutation7
    mixedMoment B raw38746step0 raw38746step0Labels = mixedMoment B raw38746step1 raw38746step1Labels := by
      have ha : raw38746step1 = -raw38746step0 := by apply Matrix.ext; change ∀ i j, raw38746step1 i j = -(raw38746step0 i j); unfold raw38746step1 raw38746step0; decide +kernel
      have hl : raw38746step1Labels = raw38746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38746step1 raw38746step1Labels = mixedMoment B raw38746step2 raw38746step2Labels := by
      have ha : raw38746step2 = raw38746step1 := by apply Matrix.ext; unfold raw38746step2 raw38746step1; decide +kernel
      have hl : raw38746step1Labels = labelEmbedding4 ∘ raw38746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38746step1 raw38746step1Labels raw38746step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2067 node2067Labels := by rfl

def raw38747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38747Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38747 raw38747Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw38747 raw38747Labels = mixedMoment B raw38747step0 raw38747step0Labels := by
      have ha : raw38747step0 = raw38747 := by apply Matrix.ext; unfold raw38747step0 raw38747; decide +kernel
      have hl : raw38747Labels = labelEmbedding2 ∘ raw38747step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38747 raw38747Labels raw38747step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw38748 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38748Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw38748step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw38748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38748 raw38748Labels = mixedMoment B node1920 node1920Labels := by
  calc
    mixedMoment B raw38748 raw38748Labels = mixedMoment B raw38748step0 raw38748step0Labels := by
      have ha : raw38748step0 = (fun i j => raw38748 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38748step0 raw38748; decide +kernel
      have hl : raw38748step0Labels = raw38748Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38748 raw38748Labels permutation149 permutation7
    mixedMoment B raw38748step0 raw38748step0Labels = mixedMoment B raw38748step1 raw38748step1Labels := by
      have ha : raw38748step1 = raw38748step0 := by apply Matrix.ext; unfold raw38748step1 raw38748step0; decide +kernel
      have hl : raw38748step0Labels = labelEmbedding4 ∘ raw38748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38748step0 raw38748step0Labels raw38748step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1920 node1920Labels := by rfl

def raw38749 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38749Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38749 raw38749Labels = mixedMoment B node1800 node1800Labels := by
  calc
    mixedMoment B raw38749 raw38749Labels = mixedMoment B raw38749step0 raw38749step0Labels := by
      have ha : raw38749step0 = raw38749 := by apply Matrix.ext; unfold raw38749step0 raw38749; decide +kernel
      have hl : raw38749Labels = labelEmbedding2 ∘ raw38749step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38749 raw38749Labels raw38749step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1800 node1800Labels := by rfl

def raw38750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38750Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw38750step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw38750step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw38750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38750 raw38750Labels = mixedMoment B node2068 node2068Labels := by
  calc
    mixedMoment B raw38750 raw38750Labels = mixedMoment B raw38750step0 raw38750step0Labels := by
      have ha : raw38750step0 = (fun i j => raw38750 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38750step0 raw38750; decide +kernel
      have hl : raw38750step0Labels = raw38750Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38750 raw38750Labels permutation38 permutation7
    mixedMoment B raw38750step0 raw38750step0Labels = mixedMoment B raw38750step1 raw38750step1Labels := by
      have ha : raw38750step1 = -raw38750step0 := by apply Matrix.ext; change ∀ i j, raw38750step1 i j = -(raw38750step0 i j); unfold raw38750step1 raw38750step0; decide +kernel
      have hl : raw38750step1Labels = raw38750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38750step1 raw38750step1Labels = mixedMoment B raw38750step2 raw38750step2Labels := by
      have ha : raw38750step2 = raw38750step1 := by apply Matrix.ext; unfold raw38750step2 raw38750step1; decide +kernel
      have hl : raw38750step1Labels = labelEmbedding4 ∘ raw38750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38750step1 raw38750step1Labels raw38750step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2068 node2068Labels := by rfl

def raw38751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38751Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38751 raw38751Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw38751 raw38751Labels = mixedMoment B raw38751step0 raw38751step0Labels := by
      have ha : raw38751step0 = raw38751 := by apply Matrix.ext; unfold raw38751step0 raw38751; decide +kernel
      have hl : raw38751Labels = labelEmbedding2 ∘ raw38751step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38751 raw38751Labels raw38751step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1802 node1802Labels := by rfl

def raw38752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38752Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38752step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38752step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38752step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38752 raw38752Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw38752 raw38752Labels = mixedMoment B raw38752step0 raw38752step0Labels := by
      have ha : raw38752step0 = (fun i j => raw38752 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38752step0 raw38752; decide +kernel
      have hl : raw38752step0Labels = raw38752Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38752 raw38752Labels permutation152 permutation7
    mixedMoment B raw38752step0 raw38752step0Labels = mixedMoment B raw38752step1 raw38752step1Labels := by
      have ha : raw38752step1 = -raw38752step0 := by apply Matrix.ext; change ∀ i j, raw38752step1 i j = -(raw38752step0 i j); unfold raw38752step1 raw38752step0; decide +kernel
      have hl : raw38752step1Labels = raw38752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38752step1 raw38752step1Labels = mixedMoment B raw38752step2 raw38752step2Labels := by
      have ha : raw38752step2 = raw38752step1 := by apply Matrix.ext; unfold raw38752step2 raw38752step1; decide +kernel
      have hl : raw38752step1Labels = labelEmbedding4 ∘ raw38752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38752step1 raw38752step1Labels raw38752step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

def raw38753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38753Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38753 raw38753Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw38753 raw38753Labels = mixedMoment B raw38753step0 raw38753step0Labels := by
      have ha : raw38753step0 = raw38753 := by apply Matrix.ext; unfold raw38753step0 raw38753; decide +kernel
      have hl : raw38753Labels = labelEmbedding2 ∘ raw38753step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38753 raw38753Labels raw38753step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw38754 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38754Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw38754step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38754step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38754 raw38754Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw38754 raw38754Labels = mixedMoment B raw38754step0 raw38754step0Labels := by
      have ha : raw38754step0 = (fun i j => raw38754 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38754step0 raw38754; decide +kernel
      have hl : raw38754step0Labels = raw38754Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38754 raw38754Labels permutation32 permutation7
    mixedMoment B raw38754step0 raw38754step0Labels = mixedMoment B raw38754step1 raw38754step1Labels := by
      have ha : raw38754step1 = -raw38754step0 := by apply Matrix.ext; change ∀ i j, raw38754step1 i j = -(raw38754step0 i j); unfold raw38754step1 raw38754step0; decide +kernel
      have hl : raw38754step1Labels = raw38754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38754step1 raw38754step1Labels = mixedMoment B raw38754step2 raw38754step2Labels := by
      have ha : raw38754step2 = raw38754step1 := by apply Matrix.ext; unfold raw38754step2 raw38754step1; decide +kernel
      have hl : raw38754step1Labels = labelEmbedding4 ∘ raw38754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38754step1 raw38754step1Labels raw38754step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw38755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38755Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38755 raw38755Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw38755 raw38755Labels = mixedMoment B raw38755step0 raw38755step0Labels := by
      have ha : raw38755step0 = raw38755 := by apply Matrix.ext; unfold raw38755step0 raw38755; decide +kernel
      have hl : raw38755Labels = labelEmbedding2 ∘ raw38755step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38755 raw38755Labels raw38755step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw38756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38756Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38756step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38756step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38756step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38756 raw38756Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw38756 raw38756Labels = mixedMoment B raw38756step0 raw38756step0Labels := by
      have ha : raw38756step0 = (fun i j => raw38756 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38756step0 raw38756; decide +kernel
      have hl : raw38756step0Labels = raw38756Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38756 raw38756Labels permutation152 permutation7
    mixedMoment B raw38756step0 raw38756step0Labels = mixedMoment B raw38756step1 raw38756step1Labels := by
      have ha : raw38756step1 = -raw38756step0 := by apply Matrix.ext; change ∀ i j, raw38756step1 i j = -(raw38756step0 i j); unfold raw38756step1 raw38756step0; decide +kernel
      have hl : raw38756step1Labels = raw38756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38756step1 raw38756step1Labels = mixedMoment B raw38756step2 raw38756step2Labels := by
      have ha : raw38756step2 = raw38756step1 := by apply Matrix.ext; unfold raw38756step2 raw38756step1; decide +kernel
      have hl : raw38756step1Labels = labelEmbedding4 ∘ raw38756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38756step1 raw38756step1Labels raw38756step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw38757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38757Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38757 raw38757Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw38757 raw38757Labels = mixedMoment B raw38757step0 raw38757step0Labels := by
      have ha : raw38757step0 = raw38757 := by apply Matrix.ext; unfold raw38757step0 raw38757; decide +kernel
      have hl : raw38757Labels = labelEmbedding2 ∘ raw38757step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38757 raw38757Labels raw38757step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw38758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38758Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38758step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38758step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38758 raw38758Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw38758 raw38758Labels = mixedMoment B raw38758step0 raw38758step0Labels := by
      have ha : raw38758step0 = (fun i j => raw38758 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38758step0 raw38758; decide +kernel
      have hl : raw38758step0Labels = raw38758Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38758 raw38758Labels permutation32 permutation7
    mixedMoment B raw38758step0 raw38758step0Labels = mixedMoment B raw38758step1 raw38758step1Labels := by
      have ha : raw38758step1 = -raw38758step0 := by apply Matrix.ext; change ∀ i j, raw38758step1 i j = -(raw38758step0 i j); unfold raw38758step1 raw38758step0; decide +kernel
      have hl : raw38758step1Labels = raw38758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38758step1 raw38758step1Labels = mixedMoment B raw38758step2 raw38758step2Labels := by
      have ha : raw38758step2 = raw38758step1 := by apply Matrix.ext; unfold raw38758step2 raw38758step1; decide +kernel
      have hl : raw38758step1Labels = labelEmbedding4 ∘ raw38758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38758step1 raw38758step1Labels raw38758step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw38759 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38759Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38759 raw38759Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw38759 raw38759Labels = mixedMoment B raw38759step0 raw38759step0Labels := by
      have ha : raw38759step0 = raw38759 := by apply Matrix.ext; unfold raw38759step0 raw38759; decide +kernel
      have hl : raw38759Labels = labelEmbedding2 ∘ raw38759step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38759 raw38759Labels raw38759step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw38760 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38760Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38760step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38760step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38760 raw38760Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw38760 raw38760Labels = mixedMoment B raw38760step0 raw38760step0Labels := by
      have ha : raw38760step0 = (fun i j => raw38760 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38760step0 raw38760; decide +kernel
      have hl : raw38760step0Labels = raw38760Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38760 raw38760Labels permutation32 permutation7
    mixedMoment B raw38760step0 raw38760step0Labels = mixedMoment B raw38760step1 raw38760step1Labels := by
      have ha : raw38760step1 = -raw38760step0 := by apply Matrix.ext; change ∀ i j, raw38760step1 i j = -(raw38760step0 i j); unfold raw38760step1 raw38760step0; decide +kernel
      have hl : raw38760step1Labels = raw38760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38760step1 raw38760step1Labels = mixedMoment B raw38760step2 raw38760step2Labels := by
      have ha : raw38760step2 = raw38760step1 := by apply Matrix.ext; unfold raw38760step2 raw38760step1; decide +kernel
      have hl : raw38760step1Labels = labelEmbedding4 ∘ raw38760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38760step1 raw38760step1Labels raw38760step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw38761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38761Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38761 raw38761Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw38761 raw38761Labels = mixedMoment B raw38761step0 raw38761step0Labels := by
      have ha : raw38761step0 = raw38761 := by apply Matrix.ext; unfold raw38761step0 raw38761; decide +kernel
      have hl : raw38761Labels = labelEmbedding2 ∘ raw38761step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38761 raw38761Labels raw38761step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw38762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38762Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38762step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38762step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38762 raw38762Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw38762 raw38762Labels = mixedMoment B raw38762step0 raw38762step0Labels := by
      have ha : raw38762step0 = (fun i j => raw38762 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38762step0 raw38762; decide +kernel
      have hl : raw38762step0Labels = raw38762Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38762 raw38762Labels permutation170 permutation7
    mixedMoment B raw38762step0 raw38762step0Labels = mixedMoment B raw38762step1 raw38762step1Labels := by
      have ha : raw38762step1 = -raw38762step0 := by apply Matrix.ext; change ∀ i j, raw38762step1 i j = -(raw38762step0 i j); unfold raw38762step1 raw38762step0; decide +kernel
      have hl : raw38762step1Labels = raw38762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38762step1 raw38762step1Labels = mixedMoment B raw38762step2 raw38762step2Labels := by
      have ha : raw38762step2 = raw38762step1 := by apply Matrix.ext; unfold raw38762step2 raw38762step1; decide +kernel
      have hl : raw38762step1Labels = labelEmbedding4 ∘ raw38762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38762step1 raw38762step1Labels raw38762step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

def raw38763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38763Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38763 raw38763Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw38763 raw38763Labels = mixedMoment B raw38763step0 raw38763step0Labels := by
      have ha : raw38763step0 = raw38763 := by apply Matrix.ext; unfold raw38763step0 raw38763; decide +kernel
      have hl : raw38763Labels = labelEmbedding2 ∘ raw38763step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38763 raw38763Labels raw38763step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw38764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38764Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38764step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38764step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38764 raw38764Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw38764 raw38764Labels = mixedMoment B raw38764step0 raw38764step0Labels := by
      have ha : raw38764step0 = (fun i j => raw38764 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38764step0 raw38764; decide +kernel
      have hl : raw38764step0Labels = raw38764Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38764 raw38764Labels permutation32 permutation7
    mixedMoment B raw38764step0 raw38764step0Labels = mixedMoment B raw38764step1 raw38764step1Labels := by
      have ha : raw38764step1 = -raw38764step0 := by apply Matrix.ext; change ∀ i j, raw38764step1 i j = -(raw38764step0 i j); unfold raw38764step1 raw38764step0; decide +kernel
      have hl : raw38764step1Labels = raw38764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38764step1 raw38764step1Labels = mixedMoment B raw38764step2 raw38764step2Labels := by
      have ha : raw38764step2 = raw38764step1 := by apply Matrix.ext; unfold raw38764step2 raw38764step1; decide +kernel
      have hl : raw38764step1Labels = labelEmbedding4 ∘ raw38764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38764step1 raw38764step1Labels raw38764step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

def raw38765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38765Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38765 raw38765Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw38765 raw38765Labels = mixedMoment B raw38765step0 raw38765step0Labels := by
      have ha : raw38765step0 = raw38765 := by apply Matrix.ext; unfold raw38765step0 raw38765; decide +kernel
      have hl : raw38765Labels = labelEmbedding2 ∘ raw38765step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38765 raw38765Labels raw38765step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw38766 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38766Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38766step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38766step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38766 raw38766Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw38766 raw38766Labels = mixedMoment B raw38766step0 raw38766step0Labels := by
      have ha : raw38766step0 = (fun i j => raw38766 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38766step0 raw38766; decide +kernel
      have hl : raw38766step0Labels = raw38766Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38766 raw38766Labels permutation34 permutation7
    mixedMoment B raw38766step0 raw38766step0Labels = mixedMoment B raw38766step1 raw38766step1Labels := by
      have ha : raw38766step1 = -raw38766step0 := by apply Matrix.ext; change ∀ i j, raw38766step1 i j = -(raw38766step0 i j); unfold raw38766step1 raw38766step0; decide +kernel
      have hl : raw38766step1Labels = raw38766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38766step1 raw38766step1Labels = mixedMoment B raw38766step2 raw38766step2Labels := by
      have ha : raw38766step2 = raw38766step1 := by apply Matrix.ext; unfold raw38766step2 raw38766step1; decide +kernel
      have hl : raw38766step1Labels = labelEmbedding4 ∘ raw38766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38766step1 raw38766step1Labels raw38766step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw38767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38767Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38767 raw38767Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw38767 raw38767Labels = mixedMoment B raw38767step0 raw38767step0Labels := by
      have ha : raw38767step0 = raw38767 := by apply Matrix.ext; unfold raw38767step0 raw38767; decide +kernel
      have hl : raw38767Labels = labelEmbedding2 ∘ raw38767step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38767 raw38767Labels raw38767step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw38768 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38768Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38768step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38768step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38768 raw38768Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw38768 raw38768Labels = mixedMoment B raw38768step0 raw38768step0Labels := by
      have ha : raw38768step0 = (fun i j => raw38768 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38768step0 raw38768; decide +kernel
      have hl : raw38768step0Labels = raw38768Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38768 raw38768Labels permutation32 permutation7
    mixedMoment B raw38768step0 raw38768step0Labels = mixedMoment B raw38768step1 raw38768step1Labels := by
      have ha : raw38768step1 = -raw38768step0 := by apply Matrix.ext; change ∀ i j, raw38768step1 i j = -(raw38768step0 i j); unfold raw38768step1 raw38768step0; decide +kernel
      have hl : raw38768step1Labels = raw38768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38768step1 raw38768step1Labels = mixedMoment B raw38768step2 raw38768step2Labels := by
      have ha : raw38768step2 = raw38768step1 := by apply Matrix.ext; unfold raw38768step2 raw38768step1; decide +kernel
      have hl : raw38768step1Labels = labelEmbedding4 ∘ raw38768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38768step1 raw38768step1Labels raw38768step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw38769 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38769Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38769step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38769 raw38769Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw38769 raw38769Labels = mixedMoment B raw38769step0 raw38769step0Labels := by
      have ha : raw38769step0 = raw38769 := by apply Matrix.ext; unfold raw38769step0 raw38769; decide +kernel
      have hl : raw38769Labels = labelEmbedding2 ∘ raw38769step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38769 raw38769Labels raw38769step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw38770 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38770Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38770step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw38770step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw38770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38770 raw38770Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw38770 raw38770Labels = mixedMoment B raw38770step0 raw38770step0Labels := by
      have ha : raw38770step0 = (fun i j => raw38770 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38770step0 raw38770; decide +kernel
      have hl : raw38770step0Labels = raw38770Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38770 raw38770Labels permutation31 permutation7
    mixedMoment B raw38770step0 raw38770step0Labels = mixedMoment B raw38770step1 raw38770step1Labels := by
      have ha : raw38770step1 = raw38770step0 := by apply Matrix.ext; unfold raw38770step1 raw38770step0; decide +kernel
      have hl : raw38770step0Labels = labelEmbedding4 ∘ raw38770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38770step0 raw38770step0Labels raw38770step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

def raw38771 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38771Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38771step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38771 raw38771Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw38771 raw38771Labels = mixedMoment B raw38771step0 raw38771step0Labels := by
      have ha : raw38771step0 = raw38771 := by apply Matrix.ext; unfold raw38771step0 raw38771; decide +kernel
      have hl : raw38771Labels = labelEmbedding2 ∘ raw38771step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38771 raw38771Labels raw38771step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw38772 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38772Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38772step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw38772step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw38772step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38772step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw38772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38772 raw38772Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw38772 raw38772Labels = mixedMoment B raw38772step0 raw38772step0Labels := by
      have ha : raw38772step0 = (fun i j => raw38772 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38772step0 raw38772; decide +kernel
      have hl : raw38772step0Labels = raw38772Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38772 raw38772Labels permutation8 permutation7
    mixedMoment B raw38772step0 raw38772step0Labels = mixedMoment B raw38772step1 raw38772step1Labels := by
      have ha : raw38772step1 = -raw38772step0 := by apply Matrix.ext; change ∀ i j, raw38772step1 i j = -(raw38772step0 i j); unfold raw38772step1 raw38772step0; decide +kernel
      have hl : raw38772step1Labels = raw38772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38772step1 raw38772step1Labels = mixedMoment B raw38772step2 raw38772step2Labels := by
      have ha : raw38772step2 = raw38772step1 := by apply Matrix.ext; unfold raw38772step2 raw38772step1; decide +kernel
      have hl : raw38772step1Labels = labelEmbedding4 ∘ raw38772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38772step1 raw38772step1Labels raw38772step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw38773 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38773Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38773 raw38773Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw38773 raw38773Labels = mixedMoment B raw38773step0 raw38773step0Labels := by
      have ha : raw38773step0 = raw38773 := by apply Matrix.ext; unfold raw38773step0 raw38773; decide +kernel
      have hl : raw38773Labels = labelEmbedding2 ∘ raw38773step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38773 raw38773Labels raw38773step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw38774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38774Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw38774step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw38774step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw38774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38774 raw38774Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw38774 raw38774Labels = mixedMoment B raw38774step0 raw38774step0Labels := by
      have ha : raw38774step0 = (fun i j => raw38774 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38774step0 raw38774; decide +kernel
      have hl : raw38774step0Labels = raw38774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38774 raw38774Labels permutation9 permutation7
    mixedMoment B raw38774step0 raw38774step0Labels = mixedMoment B raw38774step1 raw38774step1Labels := by
      have ha : raw38774step1 = -raw38774step0 := by apply Matrix.ext; change ∀ i j, raw38774step1 i j = -(raw38774step0 i j); unfold raw38774step1 raw38774step0; decide +kernel
      have hl : raw38774step1Labels = raw38774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38774step1 raw38774step1Labels = mixedMoment B raw38774step2 raw38774step2Labels := by
      have ha : raw38774step2 = raw38774step1 := by apply Matrix.ext; unfold raw38774step2 raw38774step1; decide +kernel
      have hl : raw38774step1Labels = labelEmbedding4 ∘ raw38774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38774step1 raw38774step1Labels raw38774step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw38775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38775Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38775 raw38775Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw38775 raw38775Labels = mixedMoment B raw38775step0 raw38775step0Labels := by
      have ha : raw38775step0 = raw38775 := by apply Matrix.ext; unfold raw38775step0 raw38775; decide +kernel
      have hl : raw38775Labels = labelEmbedding2 ∘ raw38775step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38775 raw38775Labels raw38775step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw38776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38776Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38776step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38776step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38776 raw38776Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw38776 raw38776Labels = mixedMoment B raw38776step0 raw38776step0Labels := by
      have ha : raw38776step0 = (fun i j => raw38776 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38776step0 raw38776; decide +kernel
      have hl : raw38776step0Labels = raw38776Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38776 raw38776Labels permutation152 permutation7
    mixedMoment B raw38776step0 raw38776step0Labels = mixedMoment B raw38776step1 raw38776step1Labels := by
      have ha : raw38776step1 = -raw38776step0 := by apply Matrix.ext; change ∀ i j, raw38776step1 i j = -(raw38776step0 i j); unfold raw38776step1 raw38776step0; decide +kernel
      have hl : raw38776step1Labels = raw38776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38776step1 raw38776step1Labels = mixedMoment B raw38776step2 raw38776step2Labels := by
      have ha : raw38776step2 = raw38776step1 := by apply Matrix.ext; unfold raw38776step2 raw38776step1; decide +kernel
      have hl : raw38776step1Labels = labelEmbedding4 ∘ raw38776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38776step1 raw38776step1Labels raw38776step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

def raw38777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38777Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38777 raw38777Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw38777 raw38777Labels = mixedMoment B raw38777step0 raw38777step0Labels := by
      have ha : raw38777step0 = raw38777 := by apply Matrix.ext; unfold raw38777step0 raw38777; decide +kernel
      have hl : raw38777Labels = labelEmbedding2 ∘ raw38777step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38777 raw38777Labels raw38777step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw38778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38778Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38778step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38778step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38778 raw38778Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw38778 raw38778Labels = mixedMoment B raw38778step0 raw38778step0Labels := by
      have ha : raw38778step0 = (fun i j => raw38778 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38778step0 raw38778; decide +kernel
      have hl : raw38778step0Labels = raw38778Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38778 raw38778Labels permutation153 permutation7
    mixedMoment B raw38778step0 raw38778step0Labels = mixedMoment B raw38778step1 raw38778step1Labels := by
      have ha : raw38778step1 = -raw38778step0 := by apply Matrix.ext; change ∀ i j, raw38778step1 i j = -(raw38778step0 i j); unfold raw38778step1 raw38778step0; decide +kernel
      have hl : raw38778step1Labels = raw38778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38778step1 raw38778step1Labels = mixedMoment B raw38778step2 raw38778step2Labels := by
      have ha : raw38778step2 = raw38778step1 := by apply Matrix.ext; unfold raw38778step2 raw38778step1; decide +kernel
      have hl : raw38778step1Labels = labelEmbedding4 ∘ raw38778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38778step1 raw38778step1Labels raw38778step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

def raw38779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38779Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38779 raw38779Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw38779 raw38779Labels = mixedMoment B raw38779step0 raw38779step0Labels := by
      have ha : raw38779step0 = raw38779 := by apply Matrix.ext; unfold raw38779step0 raw38779; decide +kernel
      have hl : raw38779Labels = labelEmbedding2 ∘ raw38779step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38779 raw38779Labels raw38779step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw38780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38780Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38780step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38780step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38780 raw38780Labels = mixedMoment B node1883 node1883Labels := by
  calc
    mixedMoment B raw38780 raw38780Labels = mixedMoment B raw38780step0 raw38780step0Labels := by
      have ha : raw38780step0 = (fun i j => raw38780 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38780step0 raw38780; decide +kernel
      have hl : raw38780step0Labels = raw38780Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38780 raw38780Labels permutation152 permutation7
    mixedMoment B raw38780step0 raw38780step0Labels = mixedMoment B raw38780step1 raw38780step1Labels := by
      have ha : raw38780step1 = -raw38780step0 := by apply Matrix.ext; change ∀ i j, raw38780step1 i j = -(raw38780step0 i j); unfold raw38780step1 raw38780step0; decide +kernel
      have hl : raw38780step1Labels = raw38780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38780step1 raw38780step1Labels = mixedMoment B raw38780step2 raw38780step2Labels := by
      have ha : raw38780step2 = raw38780step1 := by apply Matrix.ext; unfold raw38780step2 raw38780step1; decide +kernel
      have hl : raw38780step1Labels = labelEmbedding4 ∘ raw38780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38780step1 raw38780step1Labels raw38780step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1883 node1883Labels := by rfl

def raw38781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38781Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38781 raw38781Labels = mixedMoment B node1864 node1864Labels := by
  calc
    mixedMoment B raw38781 raw38781Labels = mixedMoment B raw38781step0 raw38781step0Labels := by
      have ha : raw38781step0 = raw38781 := by apply Matrix.ext; unfold raw38781step0 raw38781; decide +kernel
      have hl : raw38781Labels = labelEmbedding2 ∘ raw38781step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38781 raw38781Labels raw38781step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1864 node1864Labels := by rfl

def raw38782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38782Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw38782step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38782step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38782 raw38782Labels = mixedMoment B node1882 node1882Labels := by
  calc
    mixedMoment B raw38782 raw38782Labels = mixedMoment B raw38782step0 raw38782step0Labels := by
      have ha : raw38782step0 = (fun i j => raw38782 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38782step0 raw38782; decide +kernel
      have hl : raw38782step0Labels = raw38782Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38782 raw38782Labels permutation152 permutation7
    mixedMoment B raw38782step0 raw38782step0Labels = mixedMoment B raw38782step1 raw38782step1Labels := by
      have ha : raw38782step1 = -raw38782step0 := by apply Matrix.ext; change ∀ i j, raw38782step1 i j = -(raw38782step0 i j); unfold raw38782step1 raw38782step0; decide +kernel
      have hl : raw38782step1Labels = raw38782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38782step1 raw38782step1Labels = mixedMoment B raw38782step2 raw38782step2Labels := by
      have ha : raw38782step2 = raw38782step1 := by apply Matrix.ext; unfold raw38782step2 raw38782step1; decide +kernel
      have hl : raw38782step1Labels = labelEmbedding4 ∘ raw38782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38782step1 raw38782step1Labels raw38782step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1882 node1882Labels := by rfl

def raw38783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38783Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38783 raw38783Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw38783 raw38783Labels = mixedMoment B raw38783step0 raw38783step0Labels := by
      have ha : raw38783step0 = raw38783 := by apply Matrix.ext; unfold raw38783step0 raw38783; decide +kernel
      have hl : raw38783Labels = labelEmbedding2 ∘ raw38783step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38783 raw38783Labels raw38783step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1867 node1867Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
